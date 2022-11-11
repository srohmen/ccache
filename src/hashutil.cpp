// Copyright (C) 2009-2022 Joel Rosdahl and other contributors
//
// See doc/AUTHORS.adoc for a complete list of contributors.
//
// This program is free software; you can redistribute it and/or modify it
// under the terms of the GNU General Public License as published by the Free
// Software Foundation; either version 3 of the License, or (at your option)
// any later version.
//
// This program is distributed in the hope that it will be useful, but WITHOUT
// ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
// FITNESS FOR A PARTICULAR PURPOSE. See the GNU General Public License for
// more details.
//
// You should have received a copy of the GNU General Public License along with
// this program; if not, write to the Free Software Foundation, Inc., 51
// Franklin Street, Fifth Floor, Boston, MA 02110-1301 USA

#include "hashutil.hpp"

#include "Args.hpp"
#include "Config.hpp"
#include "Context.hpp"
#include "Hash.hpp"
#include "Logging.hpp"
#include "Stat.hpp"
#include "Util.hpp"
#include "Win32Util.hpp"
#include "execute.hpp"
#include "macroskip.hpp"

#include <core/exceptions.hpp>
#include <core/wincompat.hpp>
#include <fmtmacros.hpp>
#include <util/file.hpp>
#include <util/string.hpp>

#ifdef INODE_CACHE_SUPPORTED
#  include "InodeCache.hpp"
#endif

#include "third_party/blake3/blake3_cpu_supports_avx2.h"

#ifdef HAVE_UNISTD_H
#  include <unistd.h>
#endif

#ifdef HAVE_SYS_WAIT_H
#  include <sys/wait.h>
#endif

#ifdef HAVE_AVX2
#  include <immintrin.h>
#endif

namespace {

// Returns one of HASH_SOURCE_CODE_FOUND_DATE, HASH_SOURCE_CODE_FOUND_TIME or
// HASH_SOURCE_CODE_FOUND_TIMESTAMP if "_DATE__", "_TIME__" or "_TIMESTAMP__"
// starts at str[pos].
//
// Pre-condition: str[pos - 1] == '_'
int
check_for_temporal_macros_helper(std::string_view str, size_t pos)
{
  if (pos + 7 > str.length()) {
    return 0;
  }

  int found = 0;
  int macro_len = 7;
  if (memcmp(&str[pos], "_DATE__", 7) == 0) {
    found = HASH_SOURCE_CODE_FOUND_DATE;
  } else if (memcmp(&str[pos], "_TIME__", 7) == 0) {
    found = HASH_SOURCE_CODE_FOUND_TIME;
  } else if (pos + 12 <= str.length()
             && memcmp(&str[pos], "_TIMESTAMP__", 12) == 0) {
    found = HASH_SOURCE_CODE_FOUND_TIMESTAMP;
    macro_len = 12;
  } else {
    return 0;
  }

  // Check char before and after macro to verify that the found macro isn't part
  // of another identifier.
  if ((pos == 1 || (str[pos - 2] != '_' && !isalnum(str[pos - 2])))
      && (pos + macro_len == str.length()
          || (str[pos + macro_len] != '_' && !isalnum(str[pos + macro_len])))) {
    return found;
  }

  return 0;
}

int
check_for_temporal_macros_bmh(std::string_view str)
{
  int result = 0;

  // We're using the Boyer-Moore-Horspool algorithm, which searches starting
  // from the *end* of the needle. Our needles are 8 characters long, so i
  // starts at 7.
  size_t i = 7;

  while (i < str.length()) {
    // Check whether the substring ending at str[i] has the form "_....E..". On
    // the assumption that 'E' is less common in source than '_', we check
    // str[i-2] first.
    if (str[i - 2] == 'E' && str[i - 7] == '_') {
      result |= check_for_temporal_macros_helper(str, i - 6);
    }

    // macro_skip tells us how far we can skip forward upon seeing str[i] at
    // the end of a substring.
    i += macro_skip[(uint8_t)str[i]];
  }

  return result;
}

#ifdef HAVE_AVX2
#  ifndef _MSC_VER // MSVC does not need explicit enabling of AVX2.
int check_for_temporal_macros_avx2(std::string_view str)
  __attribute__((target("avx2")));
#  endif

// The following algorithm, which uses AVX2 instructions to find __DATE__,
// __TIME__ and __TIMESTAMP__, is heavily inspired by
// <http://0x80.pl/articles/simd-strfind.html>.
int
check_for_temporal_macros_avx2(std::string_view str)
{
  int result = 0;

  // Set all 32 bytes in first and last to '_' and 'E' respectively.
  const __m256i first = _mm256_set1_epi8('_');
  const __m256i last = _mm256_set1_epi8('E');

  size_t pos = 0;
  for (; pos + 5 + 32 <= str.length(); pos += 32) {
    // Load 32 bytes from the current position in the input string, with
    // block_last being offset 5 bytes (i.e. the offset of 'E' in all three
    // macros).
    const __m256i block_first =
      _mm256_loadu_si256(reinterpret_cast<const __m256i*>(&str[pos]));
    const __m256i block_last =
      _mm256_loadu_si256(reinterpret_cast<const __m256i*>(&str[pos + 5]));

    // For i in 0..31:
    //   eq_X[i] = 0xFF if X[i] == block_X[i] else 0
    const __m256i eq_first = _mm256_cmpeq_epi8(first, block_first);
    const __m256i eq_last = _mm256_cmpeq_epi8(last, block_last);

    // Set bit i in mask if byte i in both eq_first and eq_last has the most
    // significant bit set.
    uint32_t mask = _mm256_movemask_epi8(_mm256_and_si256(eq_first, eq_last));

    // A bit set in mask now indicates a possible location for a temporal macro.
    while (mask != 0) {
      // The start position + 1 (as we know the first char is _).
#  ifndef _MSC_VER
      const auto start = pos + __builtin_ctz(mask) + 1;
#  else
      unsigned long index;
      _BitScanForward(&index, mask);
      const auto start = pos + index + 1;
#  endif

      // Clear the least significant bit set.
      mask = mask & (mask - 1);

      result |= check_for_temporal_macros_helper(str, start);
    }
  }

  result |= check_for_temporal_macros_bmh(str.substr(pos));

  return result;
}
#endif

int
do_hash_file(const Context& ctx,
             Digest& digest,
             const std::string& path,
             size_t size_hint,
             bool check_temporal_macros)
{
#ifdef INODE_CACHE_SUPPORTED
  const InodeCache::ContentType content_type =
    check_temporal_macros ? InodeCache::ContentType::checked_for_temporal_macros
                          : InodeCache::ContentType::raw;
  if (ctx.config.inode_cache()) {
    int result;
    if (ctx.inode_cache.get(path, content_type, digest, &result)) {
      return result;
    }
  }
#else
  (void)ctx;
#endif

  const auto data = util::read_file<std::string>(path, size_hint);
  if (!data) {
    LOG("Failed to read {}: {}", path, data.error());
    return HASH_SOURCE_CODE_ERROR;
  }

  int result = HASH_SOURCE_CODE_OK;
  if (check_temporal_macros) {
    result |= check_for_temporal_macros(*data);
  }

  Hash hash;
  hash.hash(*data);
  digest = hash.digest();

#ifdef INODE_CACHE_SUPPORTED
  ctx.inode_cache.put(path, content_type, digest, result);
#endif

  return result;
}

struct HashPipeOutput
{
  bool
  operator()(int pipeid)
  {
    const auto hash_result = hash.hash_fd(pipeid);
    if (!hash_result) {
      LOG("Error hashing compiler check command output: {}",
          hash_result.error());
    }
    return bool(hash_result);
  }

  Hash& hash;
};

template<typename ProcessingFunc>
bool
execute_process(ProcessingFunc& process_func,
                const Args& args,
                const std::string& adjusted_command = "")
{
  // silence compiler warning
  (void)adjusted_command;

  const auto argv = args.to_argv();

#ifdef _WIN32
  PROCESS_INFORMATION pi;
  memset(&pi, 0x00, sizeof(pi));
  STARTUPINFO si;
  memset(&si, 0x00, sizeof(si));

  std::string path = find_executable_in_path(args[0], getenv("PATH"));
  if (path.empty()) {
    path = args[0];
  }
  std::string sh = win32getshell(path);
  if (!sh.empty()) {
    path = sh;
  }

  si.cb = sizeof(STARTUPINFO);

  HANDLE pipe_out[2];
  SECURITY_ATTRIBUTES sa = {sizeof(SECURITY_ATTRIBUTES), nullptr, TRUE};
  CreatePipe(&pipe_out[0], &pipe_out[1], &sa, 0);
  SetHandleInformation(pipe_out[0], HANDLE_FLAG_INHERIT, 0);
  si.hStdOutput = pipe_out[1];
  si.hStdError = pipe_out[1];
  si.hStdInput = GetStdHandle(STD_INPUT_HANDLE);
  si.dwFlags = STARTF_USESTDHANDLES;

  std::string win32args;
  if (!adjusted_command.empty()) {
    win32args = adjusted_command; // quoted
  } else {
    win32args = Win32Util::argv_to_string(argv.data(), sh);
  }
  BOOL ret = CreateProcess(path.c_str(),
                           const_cast<char*>(win32args.c_str()),
                           nullptr,
                           nullptr,
                           1,
                           0,
                           nullptr,
                           nullptr,
                           &si,
                           &pi);
  CloseHandle(pipe_out[1]);
  if (ret == 0) {
    return false;
  }
  int fd = _open_osfhandle((intptr_t)pipe_out[0], O_BINARY);

  const bool compiler_check_result = process_func(fd);
  WaitForSingleObject(pi.hProcess, INFINITE);
  DWORD exitcode;
  GetExitCodeProcess(pi.hProcess, &exitcode);
  CloseHandle(pipe_out[0]);
  CloseHandle(pi.hProcess);
  CloseHandle(pi.hThread);
  if (exitcode != 0) {
    LOG("Compiler check command returned {}", exitcode);
    return false;
  }
  return compiler_check_result;
#else
  int pipefd[2];
  if (pipe(pipefd) == -1) {
    throw core::Fatal(FMT("pipe failed: {}", strerror(errno)));
  }

  pid_t pid = fork();
  if (pid == -1) {
    throw core::Fatal(FMT("fork failed: {}", strerror(errno)));
  }

  if (pid == 0) {
    // Child.
    close(pipefd[0]);
    close(0);
    dup2(pipefd[1], 1);
    dup2(pipefd[1], 2);
    _exit(execvp(argv[0], const_cast<char* const*>(argv.data())));
    // Never reached.
  } else {
    // Parent.
    close(pipefd[1]);
    const bool process_result = process_func(pipefd[0]);
    close(pipefd[0]);

    int status;
    int result;
    while ((result = waitpid(pid, &status, 0)) != pid) {
      if (result == -1 && errno == EINTR) {
        continue;
      }
      LOG("waitpid failed: {}", strerror(errno));
      return false;
    }
    if (!WIFEXITED(status) || WEXITSTATUS(status) != 0) {
      LOG("Compiler check command returned {}", WEXITSTATUS(status));
      return false;
    }
    return process_result;
  }
#endif
}

struct ReadPipeOutput
{
  bool
  operator()(int pipeid)
  {
    const auto result = util::read_fd(
      pipeid, [this](const void* data, size_t size) {
      append_to_output(data, size);
    });

    if (!result) {
      LOG("Error hashing compiler check command output: {}",
          result.error());
    }
    return bool(result);
  }

  void append_to_output(const void* data, size_t size)
  {
    std::string_view buffer(static_cast<const char*>(data), size);
    output += buffer;
  }

  std::string& output;
};

bool
get_external_command_output(std::string& output,
                            const std::string& cmd,
                            const std::string& param)
{
  Args args;
  args.push_back(cmd);
  if (!param.empty()) {
    args.push_back(param);
  }
  ReadPipeOutput read_func{output};
  return execute_process(read_func, args);
}

std::string
get_significant_version(const std::string& full_version, const uint8_t sig_digits)
{
  const std::vector<std::string> version_elements =
      Util::split_into_strings(full_version, ".");
  const size_t n_tokens =
      std::min(version_elements.size(), (size_t)sig_digits);

  std::string version;
  if (n_tokens > 0) {
    version = version_elements.front();
  }
  for(size_t i = 1; i < n_tokens; ++i) {
    version += '.' + version_elements[i];
  }
  return version;
}

} // namespace

int
check_for_temporal_macros(std::string_view str)
{
#ifdef HAVE_AVX2
  if (blake3_cpu_supports_avx2()) {
    return check_for_temporal_macros_avx2(str);
  }
#endif
  return check_for_temporal_macros_bmh(str);
}

int
hash_source_code_file(const Context& ctx,
                      Digest& digest,
                      const std::string& path,
                      size_t size_hint)
{
  const bool check_temporal_macros =
    !ctx.config.sloppiness().is_enabled(core::Sloppy::time_macros);
  int result =
    do_hash_file(ctx, digest, path, size_hint, check_temporal_macros);

  if (!check_temporal_macros || result == HASH_SOURCE_CODE_OK
      || (result & HASH_SOURCE_CODE_ERROR)) {
    return result;
  }

  if (result & HASH_SOURCE_CODE_FOUND_TIME) {
    // We don't know for sure that the program actually uses the __TIME__ macro,
    // but we have to assume it anyway and hash the time stamp. However, that's
    // not very useful since the chance that we get a cache hit later the same
    // second should be quite slim... So, just signal back to the caller that
    // __TIME__ has been found so that the direct mode can be disabled.
    LOG("Found __TIME__ in {}", path);
    return result;
  }

  // __DATE__ or __TIMESTAMP__ found. We now make sure that the digest changes
  // if the (potential) expansion of those macros changes by computing a new
  // digest comprising the file digest and time information that represents the
  // macro expansions.

  Hash hash;
  hash.hash(digest.to_string());

  if (result & HASH_SOURCE_CODE_FOUND_DATE) {
    LOG("Found __DATE__ in {}", path);

    hash.hash_delimiter("date");
    auto now = Util::localtime();
    if (!now) {
      return HASH_SOURCE_CODE_ERROR;
    }
    hash.hash(now->tm_year);
    hash.hash(now->tm_mon);
    hash.hash(now->tm_mday);

    // If the compiler has support for it, the expansion of __DATE__ will change
    // according to the value of SOURCE_DATE_EPOCH. Note: We have to hash both
    // SOURCE_DATE_EPOCH and the current date since we can't be sure that the
    // compiler honors SOURCE_DATE_EPOCH.
    const auto source_date_epoch = getenv("SOURCE_DATE_EPOCH");
    if (source_date_epoch) {
      hash.hash(source_date_epoch);
    }
  }

  if (result & HASH_SOURCE_CODE_FOUND_TIMESTAMP) {
    LOG("Found __TIMESTAMP__ in {}", path);

    const auto stat = Stat::stat(path);
    if (!stat) {
      return HASH_SOURCE_CODE_ERROR;
    }

    auto modified_time = Util::localtime(stat.mtime());
    if (!modified_time) {
      return HASH_SOURCE_CODE_ERROR;
    }
    hash.hash_delimiter("timestamp");
#ifdef HAVE_ASCTIME_R
    char buffer[26];
    auto timestamp = asctime_r(&*modified_time, buffer);
#else
    auto timestamp = asctime(&*modified_time);
#endif
    if (!timestamp) {
      return HASH_SOURCE_CODE_ERROR;
    }
    hash.hash(timestamp);
  }

  digest = hash.digest();
  return result;
}

bool
hash_binary_file(const Context& ctx,
                 Digest& digest,
                 const std::string& path,
                 size_t size_hint)
{
  return do_hash_file(ctx, digest, path, size_hint, false)
         == HASH_SOURCE_CODE_OK;
}

bool
hash_binary_file(const Context& ctx, Hash& hash, const std::string& path)
{
  Digest digest;
  const bool success = hash_binary_file(ctx, digest, path);
  if (success) {
    hash.hash(digest.to_string());
  }
  return success;
}

bool
hash_command_output(Hash& hash,
                    const std::string& command,
                    const std::string& compiler)
{
#ifdef _WIN32
  std::string adjusted_command = util::strip_whitespace(command);

  // Add "echo" command.
  if (util::starts_with(adjusted_command, "echo")) {
    adjusted_command = FMT("cmd.exe /c \"{}\"", adjusted_command);
  } else if (util::starts_with(adjusted_command, "%compiler%")
             && compiler == "echo") {
    adjusted_command =
      FMT("cmd.exe /c \"{}{}\"", compiler, adjusted_command.substr(10));
  }
  Args args = Args::from_string(adjusted_command);
#else
  Args args = Args::from_string(command);
  std::string adjusted_command;
#endif

  for (size_t i = 0; i < args.size(); i++) {
    if (args[i] == "%compiler%") {
      args[i] = compiler;
    }
  }

  LOG("Executing compiler check command {}",
      Util::format_argv_for_logging(args.to_argv().data()));

  HashPipeOutput hash_func{hash};
  return execute_process(hash_func, args, adjusted_command);
}

bool
hash_multicommand_output(Hash& hash,
                         const std::string& command,
                         const std::string& compiler)
{
  for (const std::string& cmd : Util::split_into_strings(command, ";")) {
    if (!hash_command_output(hash, cmd, compiler)) {
      return false;
    }
  }
  return true;
}

std::optional<std::string>
get_compiler_version(const Config& conf, const std::string& compiler)
{
  // TODO: extend for other supported compilers
  // this function should work for clang, gcc and msvc already

  // msvc has no version/arch parameter to get the output directtly
  std::string arch_param;
  if (!conf.is_compiler_group_msvc())
    arch_param = "-dumpmachine";

  std::string arch_output;
  const auto arch_proc_result =
    get_external_command_output(arch_output, compiler, arch_param);
  if (!arch_proc_result) {
    return std::nullopt;
  }

  std::string arch, full_version;
  if (conf.is_compiler_group_msvc()) {
    // the first line of MSVC's default output contains something like:
    // "C/C++ Optimizing Compiler Version 19.29.30147 for x64"
    // This line contains both information, version and architecture.
    // Thus, no need to call the compiler once more.
    const std::vector<std::string_view> lines =
        Util::split_into_views(arch_output, "\r\n");
    if (lines.empty()) {
      LOG("Could not find version string in compiler output: {}", arch_output);
      return std::nullopt;
    }

    const std::string_view first_line = lines.front();
    const std::string token = "C/C++ Optimizing Compiler Version";
    const size_t pos = first_line.find(token);
    if (pos == std::string::npos) {
      LOG("Could not find version string in the compiler output: {}", first_line);
      return std::nullopt;
    }

    const std::string_view version_arch = first_line.substr(pos + token.size());
    // reduced to "19.29.30147 for x64"
    const std::vector<std::string> elements =
        Util::split_into_strings(version_arch, " ");

    if (elements.size() < 3) {
      LOG("Could not separate version from architecture output: {}",
        first_line);
      return std::nullopt;
    }
    arch = elements[2];
    full_version = elements[0];

  } else {
    std::string version_param = "-dumpversion";
    std::string version_output;
    const auto version_proc_result =
        get_external_command_output(version_output, compiler, version_param);
    if (!version_proc_result) {
      return std::nullopt;
    }

    arch = util::strip_whitespace(arch_output);
    full_version = util::strip_whitespace(version_output);
  }

  const uint8_t sig_digits = conf.compiler_version_significant_digits();
  const std::string version = get_significant_version(full_version, sig_digits);

  const std::string result = arch + "-" + version;
  return result;
}
