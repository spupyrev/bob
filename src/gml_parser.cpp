#include "dot_graph.h"

#include "common.h"
#include "logging.h"

#include <fstream>
#include <map>

using namespace std;

string getAttr(map<string, string>& attrs, const string& name) {
  if (!attrs.count(name)) {
    std::cerr << "attribute '" << name << "' not found\n";
	  throw 120;
  }
  return attrs[name];
}

map<string, string> parseAttrs(const vector<string>& lines) {
  map<string, string> attrs;
  for (auto line : lines) {
    vector<string> tmp = SplitNotNull(line, " \t\r\"");
    if (tmp.size() == 2) {
      attrs[tmp[0]] = tmp[1];
    }
  }
  return attrs;
}

void setAttr(Attr* o, map<string, string>& attrs, const string& name) {
  if (attrs.count(name)) {
	  o->setAttr(name, getAttr(attrs, name));
  }
}

void parseNode(DotGraph& graph, const vector<string>& lines) {
  map<string, string> attrs = parseAttrs(lines);
  string id = getAttr(attrs, "id");
  auto node = graph.addNode(id);
  if (attrs.count("label")) {
	  node->setAttr("label", getAttr(attrs, "label"));
	} else {
	  node->setAttr("label", id);
	}
  setAttr(node, attrs, "x");
  setAttr(node, attrs, "y");
  setAttr(node, attrs, "w");
  setAttr(node, attrs, "h");
  setAttr(node, attrs, "fill");
  setAttr(node, attrs, "color");
}

void parseEdge(DotGraph& graph, const vector<string>& lines) {
  map<string, string> attrs = parseAttrs(lines);
  string source = getAttr(attrs, "source");
  string target = getAttr(attrs, "target");
  // ignoring loops
  if (source == target) return;
  auto edge = graph.addEdge(source, target);
  setAttr(edge, attrs, "fill");
  setAttr(edge, attrs, "width");
}

bool readGmlGraphInt(istream& in, DotGraph& graph) {
  bool in_node = false;
  bool in_edge = false;

  int depth = 0;
  vector<string> buffer;

  string line;
  while (getline(in, line)) {
    vector<string> tmp = SplitNotNull(line, " \t\r\"");

    if (tmp[0] == "node") {
    	CHECK(!in_node && !in_edge, 120);
      in_node = true;
      if (tmp.size() > 1 && tmp[1] == "[") {
        depth++;
      }
    } else if (tmp[0] == "edge") {
    	CHECK(!in_node && !in_edge, 120);
      in_edge = true;
      if (tmp.size() > 1 && tmp[1] == "[") {
        depth++;
      }
    } else if (tmp[0] == "[") {
      if (in_node || in_edge) {
        depth++;
      }
    } else if (tmp[0] == "]") {
      if (in_node || in_edge) {
        depth--;
        if (depth == 0) {
          if (in_node) {
            parseNode(graph, buffer);
            in_node = false;
            buffer.clear();
          } else if (in_edge) {
	          parseEdge(graph, buffer);
            in_edge = false;
            buffer.clear();
          }
        }
      }
    } else {
      if (in_node || in_edge) {
        buffer.push_back(line);
      }
    }
  }

  return graph.nodes.size() > 0;
}

bool DotParser::readGmlGraph(istream& in, DotGraph& graph) const {
	try {
		return readGmlGraphInt(in, graph);
	} catch (int code) {
		LOG("gml file parsing exception: %d", code);
		return false;
	}
}

bool DotParser::writeGmlGraph(ostream& out, DotGraph& graph) const {
  out << "graph\n[\n";
  out << "  hierarhic 0\n";
  out << "  label \"\"\n";
  out << "  directed 0\n";

  for (size_t i = 0; i < graph.nodes.size(); i++) {
    auto& v = graph.nodes[i];
    string label = v->hasAttr("label") ? v->getAttr("label") : v->id;

    out << "  node\n  [\n";
    out << "    id " << v->id << "\n";
    out << "    label \"" << label << "\"\n";
    out << "    graphics\n";
    out << "    [\n";
    if (v->hasAttr("x")) {
      out << "      x " << v->getAttr("x") << "\n";
    }
    if (v->hasAttr("y")) {
      out << "      y " << v->getAttr("y") << "\n";
    }
    if (v->hasAttr("w")) {
      out << "      w " << v->getAttr("w") << "\n";
    }
    if (v->hasAttr("h")) {
      out << "      h " << v->getAttr("h") << "\n";
    }
    out << "      type \"ellipse\"\n";
    out << "      raisedBorder 0\n";
    if (v->hasAttr("fill")) {
      out << "      fill \"" << v->getAttr("fill") << "\"\n";
    }
    out << "      outline \"ellipse\"\n";
    out << "    ]\n";
    out << "    LabelGraphics\n";
    out << "    [\n";
    if (v->hasAttr("color")) {
      out << "      color \"" << v->getAttr("color") << "\"\n";
    }
    out << "    ]\n";
    out << "  ]\n";
  }

  for (size_t i = 0; i < graph.edges.size(); i++) {
    auto& e = graph.edges[i];
    out << "  edge\n";
    out << "  [\n";
    out << "    source " << e->source << "\n";
    out << "    target " << e->target << "\n";
    out << "    graphics\n";
    out << "    [\n";
    if (e->hasAttr("width")) {
      out << "      width " << e->getAttr("width") << "\n";
    }
    if (e->hasAttr("fill")) {
      out << "      fill \"" << e->getAttr("fill") << "\"\n";
    }
    out << "    ]\n";
    out << "  ]\n";
  }

  out << "]\n";
  return true;
}
