#include "io_graph.h"
#include "graph_parser.h"

#include "common.h"
#include "logging.h"

#include <iostream>
#include <fstream>

using namespace std;

bool ReadLines(istream& in, vector<string>& lines);
bool isSpecial(const string& line);
bool isNode(const string& line);
bool isEdge(const string& line);
IOEdge* ParseEdge(IOGraph& graph, const string& line);
IONode* ParseNode(IOGraph& graph, const string& line);
string ExtractId(const string& line);
map<string, string> ParseAttr(const string& line);
void ExtractAttr(const string& line, string& key, string& value);
void SplitLine(const string& line, string& beforeBrakets, string& insideBrackets);
vector<string> SplitAttr(const string& line, char separator);

bool readDotGraphInt(istream& in, IOGraph& graph) {
  vector<string> lines;

  if (!ReadLines(in, lines)) {
    return false;
  }

  for (size_t i = 0; i < lines.size(); i++) {
    if (isSpecial(lines[i])) {
    	continue;
      //ParseNode(graph, lines[i]);
    } else if (isEdge(lines[i])) {
      ParseEdge(graph, lines[i]);
    } else if (isNode(lines[i])) {
      ParseNode(graph, lines[i]);
    } else {
      cerr << "Unknown entry: " << lines[i] << "\n";
      return false;
    }
  }

  // make sure all nodes have labels
  for (auto& node : graph.nodes) {
    if (!node.hasAttr("label")) {
      node.setAttr("label", node.id);
    }
  }

  return true;
}

// Parse input *.dot file
// Throws 110 if parsing is not successful
bool GraphParser::readDotGraph(istream& in, IOGraph& graph) const {
  try {
    return readDotGraphInt(in, graph);
  } catch (int code) {
    LOG("dot file parsing exception: %d", code);
    return false;
  }
}

bool ReadLines(istream& in, vector<string>& res) {
  char c;
  string s = "";
  int state = -1;
  bool insideQuote = false;

  while (in.get(c)) {
    if (c == '{' && !insideQuote) {
      state = 0;
      continue;
    }

    if (c == '}' && !insideQuote) {
      if (!trim(s).empty()) res.push_back(s);
      s.clear();
      state = -1;
      continue;
    }

    if (state == 0) {
      if (c == ';' && !insideQuote) {
        if (s.length() > 0) {
          res.push_back(s);
        }

        s = "";
      } else {
        if (c == '"') {
          insideQuote = !insideQuote;
        }

        s += c;
      }
    }
  }

  return (state == -1 && !insideQuote && res.size() > 0);
}

bool isSpecial(const string& line) {
  string beforeBrakets, insideBrackets;
  SplitLine(line, beforeBrakets, insideBrackets);
  string s = trim(beforeBrakets);

  if (s == "node") {
    return true;
  }

  if (s == "graph") {
    return true;
  }

  if (s == "edge") {
    return true;
  }

  return false;
}

// Locate edge operators outside quoted node identifiers.
static vector<size_t> edgeOperators(const string& text) {
  vector<size_t> result;
  bool quoted = false;
  for (size_t i = 0; i < text.size(); ++i) {
    if (quoted && text[i] == '\\' && i + 1 < text.size()) { ++i; continue; }
    if (text[i] == '"') quoted = !quoted;
    if (!quoted && i + 1 < text.size() && text[i] == '-' &&
        (text[i + 1] == '-' || text[i + 1] == '>')) {
      result.push_back(i++);
    }
  }
  return result;
}

bool isNode(const string& line) {
  return !isEdge(line);
}

bool isEdge(const string& line) {
  string beforeBrakets, insideBrackets;
  SplitLine(line, beforeBrakets, insideBrackets);
  return !edgeOperators(beforeBrakets).empty();
}

string ExtractId(const string& line) {
  string s = trim(line);

  if (s[0] == '"') {
    CHECK(s[s.length() - 1] == '"', 110);
    return s.substr(1, s.length() - 2);
  }

  return s;
}

IOEdge* ParseEdge(IOGraph& graph, const string& line) {
  string beforeBrakets, insideBrackets;
  SplitLine(line, beforeBrakets, insideBrackets);
  const auto operators = edgeOperators(beforeBrakets);
  CHECK(!operators.empty(), "missing DOT edge operator");
  vector<string> ids;
  size_t start = 0;
  for (size_t at : operators) {
    const string id = trim(beforeBrakets.substr(start, at - start));
    CHECK(!id.empty(), "missing DOT edge endpoint");
    ids.push_back(ExtractId(id));
    start = at + 2;
  }
  const string last = trim(beforeBrakets.substr(start));
  CHECK(!last.empty(), "missing DOT edge endpoint");
  ids.push_back(ExtractId(last));
  const auto attrs = ParseAttr(insideBrackets);
  IOEdge* edge = nullptr;
  for (size_t i = 1; i < ids.size(); ++i) {
    edge = graph.addEdge(ids[i - 1], ids[i]);
    edge->setAttr(attrs);
  }
  return edge;
}

IONode* ParseNode(IOGraph& graph, const string& line) {
  string beforeBrakets, insideBrackets;
  SplitLine(line, beforeBrakets, insideBrackets);

  string id = ExtractId(beforeBrakets);
  auto node = graph.getOrCreateNode(id);

  auto attrs = ParseAttr(insideBrackets);
  node->setAttr(attrs);
  if (attrs.count("label") == 0) {
    node->setAttr("label", id);
  }
  return node;
}

map<string, string> ParseAttr(const string& line) {
  string s = trim(line);
  vector<string> tmp = SplitAttr(s, ',');
  map<string, string> attr;

  for (int i = 0; i < (int)tmp.size(); i++) {
    string key, value;
    ExtractAttr(tmp[i], key, value);
    attr[key] = value;
  }

  return attr;
}

void ExtractAttr(const string& line, string& key, string& value) {
  vector<string> tmp = SplitAttr(line, '=');
  CHECK(tmp.size() == 2, 110);
  key = trim(tmp[0]);
  value = ExtractId(tmp[1]);
}

void SplitLine(const string& line, string& beforeBrakets, string& insideBrackets) {
  beforeBrakets = insideBrackets = "";
  int i = 0;
  bool insideQuote = false;

  while (i < (int)line.length()) {
    if (line[i] == '[' && !insideQuote) {
      break;
    }

    if (line[i] == '"') {
      insideQuote = !insideQuote;
    }

    i++;
  }

  beforeBrakets = line.substr(0, i);
  CHECK(!insideQuote, 110);
  int j = i;

  while (j < (int)line.length()) {
    if (line[j] == ']' && !insideQuote) {
      break;
    }

    if (line[j] == '"') {
      insideQuote = !insideQuote;
    }

    j++;
  }

  if (j - i - 1 > 0) {
    insideBrackets = line.substr(i + 1, j - i - 1);
  }
}

vector<string> SplitAttr(const string& line, char separator) {
  vector<string> res;
  bool insideQuotes = false;
  string s = "";

  for (int i = 0; i < (int)line.length(); i++) {
    if (!insideQuotes) {
      if (line[i] == '"') {
        insideQuotes = true;
        s += line[i];
        continue;
      }

      if (line[i] == separator) {
        if (s.length() > 0) {
          res.push_back(s);
        }

        s = "";
        continue;
      }

      s += line[i];
    } else {
      if (line[i] == '"') {
        insideQuotes = false;
      }

      s += line[i];
    }
  }

  if (s.length() > 0) {
    res.push_back(s);
  }

  return res;
}

void WriteStyles(ostream& out, IOGraph& g);
void WriteNodes(ostream& out, IOGraph& g);
void WriteStyle(ostream& out, const IONode& n, bool useQ);
void WriteNode(ostream& out, const IONode& n, bool useQ);
void WriteAttr(ostream& out, const map<string, string>& attr);
void WriteEdges(ostream& out, IOGraph& g);
void WriteEdge(ostream& out, const IOEdge& n);

bool GraphParser::writeDotGraph(ostream& out, IOGraph& graph) const {
  out << "graph {\n";
  WriteStyles(out, graph);
  WriteNodes(out, graph);
  WriteEdges(out, graph);
  out << "}\n";
  return true;
}

void WriteStyles(ostream& out, IOGraph& g) {
  for (size_t i = 0; i < g.style.size(); i++) {
    WriteStyle(out, g.style[i], false);
  }
}

void WriteNodes(ostream& out, IOGraph& g) {
  for (size_t i = 0; i < g.nodes.size(); i++) {
    WriteNode(out, g.nodes[i], true);
  }
}

void WriteStyle(ostream& out, const IONode& n, bool useQ) {
  if (useQ) {
    out << "  \"" << n.id << "\" ";
  } else {
    out << "  " << n.id << " ";
  }

  WriteAttr(out, n.attr);
  out << ";\n";
}

void WriteNode(ostream& out, const IONode& n, bool useQ) {
  if (useQ) {
    out << "  \"" << n.id << "\" ";
  } else {
    out << "  " << n.id << " ";
  }

  if (n.attr.size() > 0) {
    WriteAttr(out, n.attr);
  }

  out << ";\n";
}

void WriteAttr(ostream& out, const map<string, string>& attr) {
  out << "[";

  for (auto iter = attr.begin(); iter != attr.end(); iter++) {
    string key = (*iter).first;
    string value = (*iter).second;

    if (iter != attr.begin()) {
      out << ", ";
    }

    out << key << "=\"" << value << "\"";
  }

  out << "]";
}

void WriteEdges(ostream& out, IOGraph& g) {
  for (size_t i = 0; i < g.edges.size(); i++) {
    WriteEdge(out, g.edges[i]);
  }
}

void WriteEdge(ostream& out, const IOEdge& e) {
  out << "  \"" << e.source << "\" -- \"" << e.target << "\" ";

  if (e.attr.size() > 0) {
    WriteAttr(out, e.attr);
  }

  out << ";\n";
}
