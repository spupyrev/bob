#include "planar_graph.h"

namespace {

bool equal(double x1, double y1, double x2, double y2) {
  return Abs(x1 - x2) < EPS && Abs(y1 - y2) < EPS;
}

bool SolveLinearSystem(double a00, double a01, double b0, double a10, double a11, double b1, double& x, double& y) {
  double d = a00 * a11 - a10 * a01;

  if (Abs(d) < EPS) {
    x = y = 0;
    return false;
  }

  x = (b0 * a11 - b1 * a01) / d;
  y = (a00 * b1 - a10 * b0) / d;
  return true;
}

bool cross(IOGraph& graph, IOEdge* e1, IOEdge* e2) {
  if (e1->hasAttr("x") || e2->hasAttr("x")) {
    return false;
  }

  double ax = graph.getNode(e1->source)->getDoubleAttr("x");
  double ay = graph.getNode(e1->source)->getDoubleAttr("y");
  double bx = graph.getNode(e1->target)->getDoubleAttr("x");
  double by = graph.getNode(e1->target)->getDoubleAttr("y");
  double cx = graph.getNode(e2->source)->getDoubleAttr("x");
  double cy = graph.getNode(e2->source)->getDoubleAttr("y");
  double dx = graph.getNode(e2->target)->getDoubleAttr("x");
  double dy = graph.getNode(e2->target)->getDoubleAttr("y");

  if (equal(ax, ay, cx, cy) || equal(ax, ay, dx, dy)) {
    return false;
  }

  if (equal(bx, by, cx, cy) || equal(bx, by, dx, dy)) {
    return false;
  }

  double u, v;
  bool ret = SolveLinearSystem(bx - ax, cx - dx, cx - ax, by - ay, cy - dy, cy - ay, u, v);

  if (ret && u > -EPS && u < 1.0 + EPS && v > -EPS && v < 1.0 + EPS) {
    return true;
  }

  return false;
}

struct CWComparator {
  IOGraph* ioGraph;
  map<const Edge*, IOEdge*> e2e;
  Vertex* center;
  double cx;
  double cy;

  CWComparator(IOGraph* ioGraph_, map<const Edge*, IOEdge*>& e2e_, Vertex* center_) {
    ioGraph = ioGraph_;
    e2e = e2e_;
    center = center_;
    cx = ioGraph->nodes[center->index].getDoubleAttr("x");
    cy = ioGraph->nodes[center->index].getDoubleAttr("y");
  }

  inline bool operator()(const Edge* e1, const Edge* e2) const {
    auto a = e1->other(center);
    auto b = e2->other(center);
    double ax = ioGraph->nodes[a->index].getDoubleAttr("x");
    double ay = ioGraph->nodes[a->index].getDoubleAttr("y");
    double bx = ioGraph->nodes[b->index].getDoubleAttr("x");
    double by = ioGraph->nodes[b->index].getDoubleAttr("y");
    auto e1dot = e2e.find(e1)->second;

    if (e1dot->hasAttr("x")) {
      CHECK(e1dot->hasAttr("y"));
      auto xx = SplitNotNull(e1dot->getAttr("x"), "###");
      auto yy = SplitNotNull(e1dot->getAttr("y"), "###");
      CHECK(xx.size() == yy.size() && xx.size() >= 2);

      if (e1->source == center) {
        ax = to_double(xx[1]);
        ay = to_double(yy[1]);
      } else {
        ax = to_double(xx[xx.size() - 2]);
        ay = to_double(yy[yy.size() - 2]);
      }
    }

    auto e2dot = e2e.find(e2)->second;

    if (e2dot->hasAttr("x")) {
      CHECK(e2dot->hasAttr("y"));
      auto xx = SplitNotNull(e2dot->getAttr("x"), "###");
      auto yy = SplitNotNull(e2dot->getAttr("y"), "###");
      CHECK(xx.size() == yy.size() && xx.size() >= 2);

      if (e2->source == center) {
        bx = to_double(xx[1]);
        by = to_double(yy[1]);
      } else {
        bx = to_double(xx[xx.size() - 2]);
        by = to_double(yy[yy.size() - 2]);
      }
    }

    if (ax - cx >= 0 && bx - cx < 0) {
      return true;
    }

    if (ax - cx < 0 && bx - cx >= 0) {
      return false;
    }

    if (ax - cx == 0 && bx - cx == 0) {
      if (ay - cy >= 0 || by - cy >= 0) {
        return ay > by;
      }

      return by > ay;
    }

    // compute the cross product of vectors (center -> a) x (center -> b)
    double det = (ax - cx) * (by - cy) - (bx - cx) * (ay - cy);

    if (det < 0) {
      return true;
    }

    if (det > 0) {
      return false;
    }

    // points a and b are on the same line from the center
    // check which point is closer to the center
    double d1 = (ax - cx) * (ax - cx) + (ay - cy) * (ay - cy);
    double d2 = (bx - cx) * (bx - cx) + (by - cy) * (by - cy);
    return d1 > d2;
  }
};

}  // namespace

void convertGml2Planar(PlanarGraph& graph, IOGraph& ioGraph) {
  // handle duplicate node labels
  map<string, vector<IONode*>> duplicates;

  for (auto& node : ioGraph.nodes) {
    string label = node.getAttr("label");
    duplicates[label].push_back(&node);
  }

  for (auto& pr : duplicates) {
    if (pr.second.size() <= 1) {
      continue;
    }

    int idx = 0;
    for (auto node : pr.second) {
      node->setAttr("label", pr.first + "_" + to_string(idx));
      idx++;
    }
  }

  // create nodes
  for (auto& node : ioGraph.nodes) {
    auto v = graph.newVertex();

    if (node.hasAttr("label")) {
      v->label = node.getAttr("label");
    }

    CHECK(v->index == node.index);
    CHECK(node.hasAttr("x") && node.hasAttr("y"), "input gml graph does not contain coordinates");
  }

  // create edges
  int n = graph.numberOfVertices();
  auto edges = vector<vector<Edge*>>(n, vector<Edge*>());
  map<const Edge*, IOEdge*> e2e;

  for (auto& e : ioGraph.edges) {
    auto dotU = ioGraph.getNode(e.source);
    auto dotV = ioGraph.getNode(e.target);
    auto u = graph.vertices[dotU->index];
    auto v = graph.vertices[dotV->index];

    if (graph.directed) {
      CHECK(!e.hasAttr("targetArrow") || !e.hasAttr("sourceArrow"), "bi-directed edge (%s, %s)", dotU->getAttr("label").c_str(), dotV->getAttr("label").c_str());

      if (e.hasAttr("sourceArrow") || e.hasAttr("targetArrow")) {
        if (e.hasAttr("sourceArrow")) {
          CHECK(!e.hasAttr("targetArrow"));
          swap(u, v);
        } else if (e.hasAttr("targetArrow")) {
          CHECK(!e.hasAttr("sourceArrow"));
        }
      } else {
        double sy = ioGraph.getNode(e.source)->getDoubleAttr("y");
        double ty = ioGraph.getNode(e.target)->getDoubleAttr("y");

        if (sy < ty) {
          swap(u, v);
        }
      }
    }

    auto edge = graph.newEdge(u, v);
    edges[u->index].push_back(edge);
    edges[v->index].push_back(edge);
    e2e[edge] = &e;
  }

  // verify no edges cross
  for (auto& e1 : ioGraph.edges) {
    for (auto& e2 : ioGraph.edges) {
      string errMsg = "input gml graph is not planar: ";
      errMsg += "(" + e1.source + ", " + e1.target + ") crosses ";
      errMsg += "(" + e2.source + ", " + e2.target + ")";
      CHECK(!cross(ioGraph, &e1, &e2), errMsg.c_str());
    }
  }

  // sort edges
  for (auto& v : graph.vertices) {
    auto& adj = edges[v->index];
    // sort the edges clockwise
    sort(adj.begin(), adj.end(), CWComparator(&ioGraph, e2e, v));
    reverse(adj.begin(), adj.end());
    Edge* prev = nullptr;

    for (auto& e : adj) {
      v->addEdgeAfter(e, prev);
      prev = e;
    }
  }

  for (Vertex* v : graph.vertices) {
    if (!v->edges.empty()) {
      graph.outerFace = graph.extractRightFace(v, v->edges[0]);
      break;
    }
  }
  CHECK(graph.checkConsistency(false), "parsed planar gml graph is not consistent");
}

