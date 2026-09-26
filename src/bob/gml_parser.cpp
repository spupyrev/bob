#include "io_graph.h"
#include "graph_parser.h"

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
      string key = tmp[0];
      string value = tmp[1];

      if (attrs.count(key)) {
        value = attrs[key] + "###" + value;
      }

      attrs[key] = value;
    }
  }

  return attrs;
}

void setAttr(Attr* o, map<string, string>& attrs, const string& name) {
  if (attrs.count(name)) {
    o->setAttr(name, getAttr(attrs, name));
  }
}

void parseNode(IOGraph& graph, const vector<string>& lines) {
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
  setAttr(node, attrs, "visible");
}

void parseStyle(IOGraph& graph, const vector<string>& lines) {
  map<string, string> attrs = parseAttrs(lines);
  auto style = graph.addStyle("directed");
  setAttr(style, attrs, "directed");
}

void parseEdge(IOGraph& graph, const vector<string>& lines) {
  map<string, string> attrs = parseAttrs(lines);
  string source = getAttr(attrs, "source");
  string target = getAttr(attrs, "target");

  // ignoring loops
  if (source == target) {
    return;
  }

  auto edge = graph.addEdge(source, target);
  setAttr(edge, attrs, "fill");
  setAttr(edge, attrs, "width");
  setAttr(edge, attrs, "sourceArrow");
  setAttr(edge, attrs, "targetArrow");
  setAttr(edge, attrs, "x");
  setAttr(edge, attrs, "y");
}

bool readGmlGraphInt(istream& in, IOGraph& graph) {
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
    } else if (tmp[0] == "directed" && depth == 0) {
      CHECK(!in_node && !in_edge, 120);
      parseStyle(graph, buffer);
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

bool GraphParser::readGmlGraph(istream& in, IOGraph& graph) const {
  try {
    return readGmlGraphInt(in, graph);
  } catch (int code) {
    LOG("gml file parsing exception: %d", code);
    return false;
  }
}

bool GraphParser::writeGmlGraph(ostream& out, IOGraph& graph) const {
  out << "graph\n[\n";
  out << "  hierarhic 0\n";
  out << "  label \"\"\n";
  out << "  directed 0\n";

  for (size_t i = 0; i < graph.nodes.size(); i++) {
    const auto& v = graph.nodes[i];
    string label = v.hasAttr("label") ? v.getAttr("label") : v.id;
    out << "  node\n  [\n";
    out << "    id " << v.index << "\n";
    out << "    label \"" << label << "\"\n";
    // out << "    label \"" << v.index+1 << "\"\n";
    out << "    graphics\n";
    out << "    [\n";

    if (v.hasAttr("x")) {
      out << "      x " << v.getAttr("x") << "\n";
    }

    if (v.hasAttr("y")) {
      out << "      y " << v.getAttr("y") << "\n";
    }

    if (v.hasAttr("w")) {
      out << "      w " << v.getAttr("w") << "\n";
    }

    if (v.hasAttr("h")) {
      out << "      h " << v.getAttr("h") << "\n";
    }

    if (v.getAttr("isGroup", "0") == "0") {
      out << "      type \"ellipse\"\n";
      out << "      raisedBorder 0\n";
      out << "      outline \"ellipse\"\n";
    } else {
      out << "      type \"roundrectangle\"\n";
      out << "      outline \"#000000\"\n";
      out << "      outlineStyle \"dashed\"\n";
      out << "      topBorderInset 0.0\n";
      out << "      bottomBorderInset 0.0\n";
      out << "      leftBorderInset 0.0\n";
      out << "      rightBorderInset 0.0\n";
    }

    if (v.hasAttr("fill"))
      out << "      fill \"" << v.getAttr("fill") << "\"\n";

    out << "    ]\n";
    out << "    LabelGraphics\n";
    out << "    [\n";

    if (v.hasAttr("fontSize")) {
      out << "      fontSize " << v.getAttr("fontSize") << "\n";
      out << "      fontName \"Dialog\"\n";
    }

    if (v.getAttr("isGroup", "0") == "0") {
      out << "      anchor \"c\"\n";
    } else {
      out << "      anchor \"t\"\n";
      out << "      alignment \"right\"\n";
      out << "      autoSizePolicy \"node_width\"\n";
      out << "      borderDistance 0.0\n";
      out << "      fill \"#EBEBEB\"\n";
    }

    if (v.hasAttr("color"))
      out << "      color \"" << v.getAttr("color") << "\"\n";

    if (v.hasAttr("visible"))
      out << "      visible \"" << v.getAttr("visible") << "\"\n";

    out << "    ]\n";

    if (v.hasAttr("isGroup")) {
      out << "    isGroup " << v.getAttr("isGroup") << "\n";
    }
    if (v.hasAttr("gid")) {
      out << "    gid " << v.getAttr("gid") << "\n";
    }

    out << "  ]\n";
  }

  for (size_t i = 0; i < graph.edges.size(); i++) {
    const auto& e = graph.edges[i];
    auto s = graph.getNode(e.source);
    auto t = graph.getNode(e.target);
    if (e.hasAttr("visible") && e.getAttr("visible") == "0")
      continue;
    vector<string> colors;
    if (e.hasAttr("fill")) {
      if (e.getAttr("multi", "false") == "true") {
        colors = SplitNotNull(e.getAttr("fill"), ";");
      } else {
        colors = {e.getAttr("fill")};
      }
    } else {
      colors = {""};
    }

    for (auto fillColor : colors) {
      out << "  edge\n";
      out << "  [\n";
      out << "    source " << s->index << "\n";
      out << "    target " << t->index << "\n";
      out << "    graphics\n";
      out << "    [\n";

      if (e.hasAttr("width")) {
        out << "      width " << e.getAttr("width") << "\n";
      }

      if (e.hasAttr("fill")) {
        out << "      fill \"" << fillColor << "\"\n";
      }

      if (e.hasAttr("sourceArrow")) {
        out << "      sourceArrow \"" << e.getAttr("sourceArrow") << "\"\n";
      }

      if (e.hasAttr("targetArrow")) {
        out << "      targetArrow \"" << e.getAttr("targetArrow") << "\"\n";
      }

      if (e.hasAttr("type")) {
        out << "      type \"" << e.getAttr("type") << "\"\n";
      }

      if (e.hasAttr("arcType")) {
        out << "      arcType \"" << e.getAttr("arcType") << "\"\n";
      }

      if (e.hasAttr("arcHeight")) {
        out << "      arcHeight " << e.getAttr("arcHeight") << "\n";
      }

      if (e.hasAttr("arcRatio")) {
        out << "      arcRatio " << e.getAttr("arcRatio") << "\n";
      }

      if (e.hasAttr("x")) {
        CHECK(e.hasAttr("y"));
        auto xx = SplitNotNull(e.getAttr("x"), "###");
        auto yy = SplitNotNull(e.getAttr("y"), "###");
        CHECK(xx.size() == yy.size());
        out << "      Line\n";
        out << "      [\n";

        for (size_t j = 0; j < xx.size(); j++) {
          out << "         point\n";
          out << "         [\n";
          out << "           x " << xx[j] << "\n";
          out << "           y " << yy[j] << "\n";
          out << "         ]\n";
        }

        out << "      ]\n";
      }

      out << "    ]\n";
      out << "  ]\n";
    }
  }

  out << "]\n";
  return true;
}
