/**
 * @file fuzz_shader.cpp
 * @brief libFuzzer harness for GLSL shader preprocessing and validation.
 *
 * Fuzzes shader parsing to find:
 * - Buffer overflows in preprocessor
 * - Malformed include handling
 * - Invalid directive parsing
 * - Shader compilation edge cases
 *
 * Build with:
 *   clang++ -g -O2 -fsanitize=fuzzer,address,undefined \
 *           fuzz_shader.cpp -o fuzz_shader
 *
 * Run:
 *   ./fuzz_shader corpus_shader/ -max_len=4096 -jobs=4
 */

#include <algorithm>
#include <cctype>
#include <cstdint>
#include <cstring>
#include <regex>
#include <sstream>
#include <string>
#include <string_view>
#include <unordered_map>
#include <vector>

namespace shader_fuzz {

// ============================================================================
// GLSL Preprocessor Simulator
// ============================================================================

/**
 * @brief Simple GLSL preprocessor for fuzzing.
 *
 * Simulates #include, #define, #ifdef, #endif directives.
 */
class GLSLPreprocessor {
public:
  struct PreprocessResult {
    std::string output;
    std::vector<std::string> errors;
    std::vector<std::string> warnings;
    bool success;
  };

  PreprocessResult process(const std::string &source) {
    PreprocessResult result;
    result.success = true;

    std::istringstream stream(source);
    std::string line;
    std::vector<bool> condition_stack;
    condition_stack.push_back(true); // Top-level is always active

    size_t line_num = 0;
    size_t max_lines = 10000; // Prevent infinite loops

    while (std::getline(stream, line) && line_num < max_lines) {
      ++line_num;

      // Skip empty lines
      if (line.empty() || std::all_of(line.begin(), line.end(), ::isspace)) {
        result.output += "\n";
        continue;
      }

      // Find first non-space character
      size_t first_char = line.find_first_not_of(" \t");
      if (first_char == std::string::npos) {
        result.output += "\n";
        continue;
      }

      // Check if it's a preprocessor directive
      if (line[first_char] == '#') {
        std::string directive = line.substr(first_char);

        if (!process_directive(directive, condition_stack, result, line_num)) {
          result.success = false;
        }
        result.output += "\n"; // Directives produce empty lines
      } else {
        // Regular code - only output if condition stack is all true
        bool active = std::all_of(condition_stack.begin(), condition_stack.end(),
                                  [](bool b) { return b; });
        if (active) {
          result.output += expand_macros(line) + "\n";
        } else {
          result.output += "\n";
        }
      }
    }

    // Check for unclosed conditionals
    if (condition_stack.size() > 1) {
      result.errors.push_back("Unclosed #ifdef/#ifndef at end of file");
      result.success = false;
    }

    return result;
  }

private:
  std::unordered_map<std::string, std::string> defines_;

  bool process_directive(const std::string &directive,
                         std::vector<bool> &condition_stack,
                         PreprocessResult &result,
                         size_t line_num) {
    // Parse directive type
    std::regex define_regex(R"(#\s*define\s+(\w+)(?:\s+(.*))?)", std::regex::ECMAScript);
    std::regex undef_regex(R"(#\s*undef\s+(\w+))", std::regex::ECMAScript);
    std::regex ifdef_regex(R"(#\s*ifdef\s+(\w+))", std::regex::ECMAScript);
    std::regex ifndef_regex(R"(#\s*ifndef\s+(\w+))", std::regex::ECMAScript);
    std::regex if_regex(R"(#\s*if\s+(.+))", std::regex::ECMAScript);
    std::regex else_regex(R"(#\s*else\b)", std::regex::ECMAScript);
    std::regex elif_regex(R"(#\s*elif\s+(.+))", std::regex::ECMAScript);
    std::regex endif_regex(R"(#\s*endif\b)", std::regex::ECMAScript);
    std::regex include_regex(R"(#\s*include\s+[<"]([^>"]+)[>"])", std::regex::ECMAScript);
    std::regex version_regex(R"(#\s*version\s+(\d+)(?:\s+(\w+))?)", std::regex::ECMAScript);
    std::regex extension_regex(R"(#\s*extension\s+(\w+)\s*:\s*(\w+))", std::regex::ECMAScript);

    std::smatch match;

    try {
      // #define
      if (std::regex_match(directive, match, define_regex)) {
        std::string name = match[1].str();
        std::string value = match.size() > 2 ? match[2].str() : "1";

        // Check for overly long macro names (security)
        if (name.length() > 256) {
          result.warnings.push_back("Line " + std::to_string(line_num) +
                                    ": Macro name too long, truncating");
          name = name.substr(0, 256);
        }

        defines_[name] = value;
        return true;
      }

      // #undef
      if (std::regex_match(directive, match, undef_regex)) {
        defines_.erase(match[1].str());
        return true;
      }

      // #ifdef
      if (std::regex_match(directive, match, ifdef_regex)) {
        bool defined = defines_.find(match[1].str()) != defines_.end();
        condition_stack.push_back(defined);
        return true;
      }

      // #ifndef
      if (std::regex_match(directive, match, ifndef_regex)) {
        bool defined = defines_.find(match[1].str()) != defines_.end();
        condition_stack.push_back(!defined);
        return true;
      }

      // #if (simplified - only check defined())
      if (std::regex_match(directive, match, if_regex)) {
        std::string expr = match[1].str();
        bool cond = evaluate_condition(expr);
        condition_stack.push_back(cond);
        return true;
      }

      // #else
      if (std::regex_match(directive, else_regex)) {
        if (condition_stack.size() <= 1) {
          result.errors.push_back("Line " + std::to_string(line_num) +
                                  ": #else without matching #ifdef");
          return false;
        }
        condition_stack.back() = !condition_stack.back();
        return true;
      }

      // #elif
      if (std::regex_match(directive, match, elif_regex)) {
        if (condition_stack.size() <= 1) {
          result.errors.push_back("Line " + std::to_string(line_num) +
                                  ": #elif without matching #ifdef");
          return false;
        }
        std::string expr = match[1].str();
        condition_stack.back() = evaluate_condition(expr);
        return true;
      }

      // #endif
      if (std::regex_match(directive, endif_regex)) {
        if (condition_stack.size() <= 1) {
          result.errors.push_back("Line " + std::to_string(line_num) +
                                  ": #endif without matching #ifdef");
          return false;
        }
        condition_stack.pop_back();
        return true;
      }

      // #include (validate path, don't actually include)
      if (std::regex_match(directive, match, include_regex)) {
        std::string path = match[1].str();
        if (!validate_include_path(path)) {
          result.errors.push_back("Line " + std::to_string(line_num) +
                                  ": Invalid include path: " + path);
          return false;
        }
        // In real shader, would recursively process included file
        return true;
      }

      // #version
      if (std::regex_match(directive, match, version_regex)) {
        int version = std::stoi(match[1].str());
        if (version < 100 || version > 999) {
          result.warnings.push_back("Line " + std::to_string(line_num) +
                                    ": Unusual GLSL version: " + std::to_string(version));
        }
        return true;
      }

      // #extension
      if (std::regex_match(directive, match, extension_regex)) {
        // Valid extension directive
        return true;
      }

    } catch (const std::regex_error &e) {
      result.errors.push_back("Line " + std::to_string(line_num) +
                              ": Regex error: " + std::string(e.what()));
      return false;
    } catch (const std::exception &e) {
      result.errors.push_back("Line " + std::to_string(line_num) +
                              ": Parse error: " + std::string(e.what()));
      return false;
    }

    // Unknown directive
    result.warnings.push_back("Line " + std::to_string(line_num) +
                              ": Unknown directive: " + directive);
    return true;
  }

  bool evaluate_condition(const std::string &expr) {
    // Simplified: check for "defined(X)" pattern
    std::regex defined_regex(R"(defined\s*\(\s*(\w+)\s*\))", std::regex::ECMAScript);
    std::smatch match;

    if (std::regex_search(expr, match, defined_regex)) {
      return defines_.find(match[1].str()) != defines_.end();
    }

    // Try to parse as integer
    try {
      int val = std::stoi(expr);
      return val != 0;
    } catch (...) {
      return false;
    }
  }

  bool validate_include_path(const std::string &path) {
    // Security checks for include paths
    if (path.empty() || path.length() > 256) {
      return false;
    }
    if (path.find("..") != std::string::npos) {
      return false; // No parent directory traversal
    }
    if (path[0] == '/') {
      return false; // No absolute paths
    }
    // Check for null bytes or other dangerous characters
    for (char c : path) {
      if (c == '\0' || c == '\n' || c == '\r') {
        return false;
      }
    }
    return true;
  }

  std::string expand_macros(const std::string &line) {
    std::string result = line;

    // Simple macro expansion (non-recursive, limited iterations)
    for (int iter = 0; iter < 10; ++iter) {
      bool expanded = false;
      for (const auto &[name, value] : defines_) {
        size_t pos = 0;
        while ((pos = result.find(name, pos)) != std::string::npos) {
          // Check it's a whole word
          bool left_ok = (pos == 0 || !std::isalnum(result[pos - 1]));
          bool right_ok = (pos + name.length() >= result.length() ||
                          !std::isalnum(result[pos + name.length()]));
          if (left_ok && right_ok) {
            result.replace(pos, name.length(), value);
            expanded = true;
            pos += value.length();
          } else {
            pos += name.length();
          }
        }
      }
      if (!expanded) break;
    }

    return result;
  }
};

// ============================================================================
// GLSL Lexer/Tokenizer
// ============================================================================

enum class TokenType {
  UNKNOWN,
  WHITESPACE,
  COMMENT,
  PREPROCESSOR,
  KEYWORD,
  IDENTIFIER,
  NUMBER,
  STRING,
  OPERATOR,
  PUNCTUATION,
  END_OF_FILE
};

struct Token {
  TokenType type;
  std::string value;
  size_t line;
  size_t column;
};

class GLSLLexer {
public:
  std::vector<Token> tokenize(const std::string &source) {
    std::vector<Token> tokens;
    size_t pos = 0;
    size_t line = 1;
    size_t column = 1;
    size_t max_tokens = 100000; // Prevent excessive token generation

    while (pos < source.length() && tokens.size() < max_tokens) {
      Token token;
      token.line = line;
      token.column = column;

      char c = source[pos];

      // Whitespace
      if (std::isspace(c)) {
        token.type = TokenType::WHITESPACE;
        while (pos < source.length() && std::isspace(source[pos])) {
          if (source[pos] == '\n') {
            ++line;
            column = 0;
          }
          token.value += source[pos];
          ++pos;
          ++column;
        }
        tokens.push_back(token);
        continue;
      }

      // Comments
      if (c == '/' && pos + 1 < source.length()) {
        if (source[pos + 1] == '/') {
          // Line comment
          token.type = TokenType::COMMENT;
          while (pos < source.length() && source[pos] != '\n') {
            token.value += source[pos];
            ++pos;
            ++column;
          }
          tokens.push_back(token);
          continue;
        } else if (source[pos + 1] == '*') {
          // Block comment
          token.type = TokenType::COMMENT;
          token.value = "/*";
          pos += 2;
          column += 2;
          while (pos + 1 < source.length()) {
            if (source[pos] == '*' && source[pos + 1] == '/') {
              token.value += "*/";
              pos += 2;
              column += 2;
              break;
            }
            if (source[pos] == '\n') {
              ++line;
              column = 0;
            }
            token.value += source[pos];
            ++pos;
            ++column;
          }
          tokens.push_back(token);
          continue;
        }
      }

      // Numbers
      if (std::isdigit(c) || (c == '.' && pos + 1 < source.length() &&
                               std::isdigit(source[pos + 1]))) {
        token.type = TokenType::NUMBER;
        // Handle hex, octal, decimal, float
        if (c == '0' && pos + 1 < source.length() &&
            (source[pos + 1] == 'x' || source[pos + 1] == 'X')) {
          token.value = "0x";
          pos += 2;
          column += 2;
          while (pos < source.length() && std::isxdigit(source[pos])) {
            token.value += source[pos];
            ++pos;
            ++column;
          }
        } else {
          while (pos < source.length() &&
                 (std::isdigit(source[pos]) || source[pos] == '.' ||
                  source[pos] == 'e' || source[pos] == 'E' ||
                  source[pos] == 'f' || source[pos] == 'F' ||
                  ((source[pos] == '+' || source[pos] == '-') &&
                   pos > 0 && (source[pos-1] == 'e' || source[pos-1] == 'E')))) {
            token.value += source[pos];
            ++pos;
            ++column;
          }
        }
        tokens.push_back(token);
        continue;
      }

      // Identifiers and keywords
      if (std::isalpha(c) || c == '_') {
        token.value += c;
        ++pos;
        ++column;
        while (pos < source.length() &&
               (std::isalnum(source[pos]) || source[pos] == '_')) {
          token.value += source[pos];
          ++pos;
          ++column;
        }
        token.type = is_keyword(token.value) ? TokenType::KEYWORD : TokenType::IDENTIFIER;
        tokens.push_back(token);
        continue;
      }

      // Operators and punctuation
      token.type = TokenType::OPERATOR;
      token.value = c;
      ++pos;
      ++column;

      // Multi-character operators
      if (pos < source.length()) {
        std::string two_char = std::string(1, c) + source[pos];
        if (two_char == "++" || two_char == "--" || two_char == "==" ||
            two_char == "!=" || two_char == "<=" || two_char == ">=" ||
            two_char == "&&" || two_char == "||" || two_char == "<<" ||
            two_char == ">>" || two_char == "+=" || two_char == "-=" ||
            two_char == "*=" || two_char == "/=") {
          token.value = two_char;
          ++pos;
          ++column;
        }
      }

      tokens.push_back(token);
    }

    Token eof;
    eof.type = TokenType::END_OF_FILE;
    eof.line = line;
    eof.column = column;
    tokens.push_back(eof);

    return tokens;
  }

private:
  bool is_keyword(const std::string &word) {
    static const std::vector<std::string> keywords = {
      // GLSL types
      "void", "bool", "int", "uint", "float", "double",
      "vec2", "vec3", "vec4", "dvec2", "dvec3", "dvec4",
      "ivec2", "ivec3", "ivec4", "uvec2", "uvec3", "uvec4",
      "bvec2", "bvec3", "bvec4",
      "mat2", "mat3", "mat4", "mat2x2", "mat2x3", "mat2x4",
      "mat3x2", "mat3x3", "mat3x4", "mat4x2", "mat4x3", "mat4x4",
      "sampler1D", "sampler2D", "sampler3D", "samplerCube",
      "sampler1DShadow", "sampler2DShadow", "samplerCubeShadow",
      // Qualifiers
      "const", "in", "out", "inout", "uniform", "varying", "attribute",
      "centroid", "flat", "smooth", "noperspective",
      "layout", "shared", "packed", "std140", "std430",
      "coherent", "volatile", "restrict", "readonly", "writeonly",
      "lowp", "mediump", "highp", "precision",
      // Control flow
      "if", "else", "switch", "case", "default",
      "for", "while", "do", "break", "continue", "return", "discard",
      // Other
      "struct", "true", "false"
    };
    return std::find(keywords.begin(), keywords.end(), word) != keywords.end();
  }
};

} // namespace shader_fuzz

// ============================================================================
// Fuzzer Entry Point
// ============================================================================

extern "C" int LLVMFuzzerTestOneInput(const uint8_t *data, size_t size) {
  if (size < 4 || size > 65536) {
    return 0;
  }

  // Convert to string
  std::string source(reinterpret_cast<const char *>(data), size);

  // Determine which fuzzer to run based on first byte
  uint8_t selector = data[0] % 3;

  switch (selector) {
  case 0: {
    // Fuzz preprocessor
    shader_fuzz::GLSLPreprocessor preprocessor;
    auto result = preprocessor.process(source);
    // Access results to prevent optimization
    (void)result.success;
    (void)result.output.length();
    break;
  }
  case 1: {
    // Fuzz lexer
    shader_fuzz::GLSLLexer lexer;
    auto tokens = lexer.tokenize(source);
    (void)tokens.size();
    break;
  }
  case 2: {
    // Fuzz both
    shader_fuzz::GLSLPreprocessor preprocessor;
    auto pp_result = preprocessor.process(source);
    if (pp_result.success) {
      shader_fuzz::GLSLLexer lexer;
      auto tokens = lexer.tokenize(pp_result.output);
      (void)tokens.size();
    }
    break;
  }
  }

  return 0;
}
