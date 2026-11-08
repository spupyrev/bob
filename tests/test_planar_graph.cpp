#include "planar_graph.h"
#include "graph_algorithms.h"
#include "graph_parser.h"

#include <fstream>
#include <sstream>

int main(int argc, char** argv) {
  try {
    CHECK(argc == 2, "expected a temporary input file path");
    const string path = argv[1];
    PlanarGraph triangle;
    triangle.readEdges(vector<vector<int>>{{1, 2}, {2, 0}, {0, 1}});
    CHECK(triangle.extractFaces().size() == 2);
    CHECK(triangle.extractFaces(false).size() == 1);
    CHECK(triangle.outerFace != triangle.extractLeftFace(
        triangle.outerFace.vertices[0], triangle.outerFace.edges[0]));
    CHECK(!triangle.is3Connected());

    PlanarGraph tree;
    tree.readEdges(vector<vector<int>>{{1, 2, 3}, {0}, {0}, {0}});
    CHECK(tree.extractFaces().size() == 1);
    tree.triangulate();
    CHECK(tree.numberOfVertices() == 4 && tree.numberOfEdges() == 6);
    CHECK(tree.extractFaces().size() == 4 && tree.outerFace.length() == 3);

    PlanarGraph cycle;
    cycle.readEdges(vector<vector<int>>{{1, 3}, {2, 0}, {3, 1}, {0, 2}});
    cycle.triangulateByStellation(false);
    CHECK(cycle.outerFace.length() == 3);
    CHECK(cycle.outerFace == cycle.extractRightFace(
        cycle.outerFace.vertices[0], cycle.outerFace.edges[0]));

    {
      ofstream out(path);
      out << "4 3\n3 -\n2 0,1\n0 1,2\n1 2,0\n";
    }
    PlanarGraph disconnected;
    disconnected.readEdges(path);
    CHECK(disconnected.vertices[3]->degree() == 0);
    CHECK(!disconnected.isConnected() && !disconnected.is2Connected());
    CHECK(!is2Connected(4, {{0, 1}, {1, 2}, {0, 2}}));
    std::ostringstream serialized;
    disconnected.writeEdges(serialized);
    CHECK(serialized.str().find("3 -\n") != string::npos);
    {
      ofstream out(path);
      out << "1 0\n0 -\n";
    }
    PlanarGraph isolated;
    isolated.readEdges(path);
    CHECK(isolated.numberOfVertices() == 1 && isolated.outerFace.empty());

    // Small coordinates exercise angular sorting without integer truncation.
    {
      ofstream out(path);
      out << "graph [\n\n"
          << "node [\n id 0\n graphics [\n x 0.0\n y 0.0\n ]\n ]\n"
          << "node [\n id 1\n graphics [\n x 0.3\n y 0.0\n ]\n ]\n"
          << "node [\n id 2\n graphics [\n x 0.0\n y 0.3\n ]\n ]\n"
          << "node [\n id 3\n graphics [\n x 0.1\n y 0.1\n ]\n ]\n";
      for (int u = 0; u < 4; u++) {
        for (int v = u + 1; v < 4; v++) {
          out << "edge [\n source " << u << "\n target " << v << "\n ]\n";
        }
      }
      out << "]\n";
    }
    PlanarGraph gml;
    gml.readGML(path);
    CHECK(gml.numberOfVertices() == 4 && gml.numberOfEdges() == 6);
    CHECK(gml.extractFaces().size() == 4 && !gml.outerFace.empty());
    GraphParser parser;
    IOGraph malformed;
    std::istringstream nested("graph [\nnode [\nnode [\n");
    CHECK(!parser.readGmlGraph(nested, malformed));
    malformed.clear();
    std::istringstream unfinished("graph [\nnode [\nid 0\n");
    CHECK(!parser.readGmlGraph(unfinished, malformed));
    std::cout << "Planar graph regression tests passed.\n";
  } catch (int code) {
    return code;
  }
  return 0;
}
