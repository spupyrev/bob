#pragma once

#include <cassert>
#include <cctype>
#include <iostream>
#include <memory>
#include <regex>
#include <string>
#include <vector>
#include <unordered_map>

/// A header-only implementation of parsing command-line options
class CMDOptions {
 private:
  // Custom usage text printed before the option list.
  std::string usageMessage;

  // Valid option names and their help text.
  std::unordered_map<std::string, std::string> knownOptions;

  // Registration order used to print help consistently.
  std::vector<std::string> optionOrder;

  // Values explicitly provided by parse() or setters; defaults are stored separately.
  std::unordered_map<std::string, std::string> values;

  // Fallback values for options not present in values.
  std::unordered_map<std::string, std::string> defaultValues;

  // Per-option whitelist of accepted values or regular expressions.
  std::unordered_map<std::string, std::vector<std::string> > allowedValuesByOption;

  CMDOptions(const CMDOptions&) = delete;
  CMDOptions& operator = (const CMDOptions&) = delete;
  CMDOptions() {}

 public:
  // Creates an options parser instance.
  static std::unique_ptr<CMDOptions> create() {
    return std::unique_ptr<CMDOptions>(new CMDOptions());
  }

  // Parses command-line arguments and handles help requests.
  void parse(int argc, char** argv) {
    for (int i = 1; i < argc; i++) {
      std::string s(argv[i]);

      if (s == "/?"  || s == "-?" || s == "--help" || s == "-help" || s == "--h" || s == "-h") {
        usage(argv[0]);
        throw 0;
      }

      parseOption(s);
    }
  }

  // Sets the usage text printed before the option list.
  void setUsageMessage(const std::string& msg) {
    usageMessage = msg;
  }

  // Registers an option with a default value.
  void registerOption(const std::string& optionName, const std::string& defaultValue, const std::string& description) {
    registerOption(optionName, description);
    defaultValues[optionName] = defaultValue;
  }

  // Registers a required option without a default value.
  void registerOption(const std::string& optionName, const std::string& description) {
    assert(!knownOptions.count(optionName));
    knownOptions[optionName] = description;
    optionOrder.push_back(optionName);
  }

  // Adds an accepted value or regular expression for an option.
  void registerAllowedValue(const std::string& optionName, const std::string& value) {
    assert(knownOptions.count(optionName));
    allowedValuesByOption[optionName].push_back(value);
  }

  // Sets an explicit string value for an option.
  void setStr(const std::string& optionName, const std::string& value) {
    if (!knownOptions.count(optionName)) {
      unrecognizedOption(optionName);
    }

    setOption(optionName, value);
  }

  // Returns an option value as a string.
  std::string getStr(const std::string& optionName) const {
    return getOption(optionName);
  }

  // Returns an option value as an integer.
  int getInt(const std::string& optionName) const {
    return std::stoi(getOption(optionName));
  }

  // Sets an explicit integer value for an option.
  void setInt(const std::string& optionName, int value) {
    if (!knownOptions.count(optionName)) {
      unrecognizedOption(optionName);
    }

    setOption(optionName, std::to_string(value));
  }

  // Returns an option value as a boolean.
  bool getBool(const std::string& optionName) const {
    if (!knownOptions.count(optionName)) {
      unrecognizedOption(optionName);
    }

    if (values.count(optionName)) {
      std::string value = values.find(optionName)->second;
      toLower(value);
      // Explicit values are true except these false spellings.
      return value != "false" && value != "0" && value != "no";
    }

    if (!defaultValues.count(optionName)) {
      unspecifiedOption(optionName);
    }

    std::string value = defaultValues.find(optionName)->second;
    toLower(value);
    return value == "true" || value == "1" || value == "yes";
  }

  // Sets an explicit boolean value for an option.
  void setBool(const std::string& optionName, bool value) {
    if (!knownOptions.count(optionName)) {
      unrecognizedOption(optionName);
    }

    setOption(optionName, value ? "true" : "false");
  }

  // Returns whether a known option was explicitly provided or set.
  bool isSpecified(const std::string& optionName) const {
    if (!knownOptions.count(optionName)) {
      unrecognizedOption(optionName);
    }

    return values.count(optionName) > 0;
  }

  // Returns whether a custom option was explicitly provided or set.
  bool hasCustomValue(const std::string& optionName) const {
    return values.count(optionName) > 0;
  }

private:
  void parseOption(const std::string& s) {
    const size_t equalIndex = s.find('=');
    std::string name = s.substr(0, equalIndex);

    // custom option
    if (name.substr(0, 2) == "-C") {
      if (name.find('_') != std::string::npos) {
        std::cout << "custom options cannot use underscores: " << name << "\n";
        throw 1;
      }
      name = name.substr(2);
    } else {
      if (!knownOptions.count(name)) {
        if (equalIndex == std::string::npos && knownOptions.count("")) {
          values[""] = name;
          return;
        }

        unrecognizedOption(name);
      }
    }

    std::string value = (equalIndex == std::string::npos ? "" : s.substr(equalIndex + 1));

    if (!allowedValuesByOption[name].empty()) {
      bool found = false;
      for (std::string& allowedValue : allowedValuesByOption[name]) {
        // check exact match
        if (allowedValue == value) {
          found = true;
          break;
        }
        // check regexp
        if (std::regex_match(value, std::regex(allowedValue))) {
          found = true;
          break;
        }
      }
      if (!found) {
        invalidOption(name, value);
      }
    }

    if (!values.count(name)) {
      values[name] = value;
    }
  }

  std::string getOption(const std::string& optionName) const {
    if (!knownOptions.count(optionName)) {
      unrecognizedOption(optionName);
    }

    if (values.count(optionName)) {
      return values.find(optionName)->second;
    }

    if (defaultValues.count(optionName)) {
      return defaultValues.find(optionName)->second;
    }

    unspecifiedOption(optionName);
    return "";
  }

  void setOption(const std::string& optionName, const std::string& value) {
    values[optionName] = value;
  }

  void toLower(std::string& value) const {
    for (char& c : value) {
      c = static_cast<char>(std::tolower(static_cast<unsigned char>(c)));
    }
  }

  void unspecifiedOption(const std::string& optionName) const {
    std::cout << "required option \"" << optionName << "\" is not specified\n";
    throw 1;
  }

  void unrecognizedOption(const std::string& optionName) const {
    std::cout << "unrecognized option \"" << optionName << "\"\n";
    throw 1;
  }

  void invalidOption(const std::string& optionName, const std::string& value) const {
    std::cout << "value \"" << value << "\" is invalid for option \"" << optionName << "\"\n";
    throw 1;
  }

  void usage(const std::string& program) const {
    if (usageMessage != "") {
      std::cout << usageMessage << "\n";
    } else {
      std::cout << "Usage: " << program << " [options]" << "\n";
    }

    std::cout << "Allowed options:";

    for (auto opt : optionOrder) {
      std::string name = knownOptions.find(opt)->first;

      if (name.length() == 0) {
        continue;
      }

      std::cout << "\n";
      std::cout << "  " << name;

      if (allowedValuesByOption.count(name)) {
        auto av = allowedValuesByOption.find(name)->second;

        if (!av.empty()) {
          std::cout << "=";
          bool first = true;

          for (std::string s : av)
            if (first)
            { std::cout << "[" << s; first = false; }
            else {
              std::cout << "|" << s;
            }

          std::cout << "]";
        }
      }

      std::cout << "\n";
      std::cout << "  " << knownOptions.find(opt)->second;
      if (defaultValues.count(opt)) {
        std::cout << " (default: " << defaultValues.find(opt)->second << ")";
      }
      std::cout << "\n";
    }
  }
};
