#include "bob/logging.h"
#include "bob/cmd_options.h"
#include "planar_graph.h"
#include "graph_generator.h"
#include "layout_cli.h"

#include <sstream>
#include <string>
#include <vector>
#include <chrono>
#include <cerrno>
#include <fcntl.h>
#include <limits>
#include <unistd.h>

using namespace std;

static void prepareOptions(CMDOptions& options, const LayoutCLI& cli) {
  options.setUsageMessage("Usage: " + cli.name + " [options]");

  options.registerOption("-n", "20", "Vertex count (an approximate target for 4connected)");
  options.registerOption("-verbose", "0", "Output debug info");
  options.registerOption("-seed", "0", "Random seed");
  options.registerOption("-graphs", "1", "How many graphs to process");
  options.registerOption("-graph-type", "max-planar",
                         "Test graph: max-planar, random-p3t, complete-p3t, 4connected, partial-p3t-2connected, partial-p3t-connected, planar-cubic, outerplanar-max, path, star, or matching");
  options.registerOption("-i", "",
                         "Graph input: .dot, .edges/clockwise lists, or .gml with coordinates");
  options.registerOption("-o", "",
                         "Export the layout or generated graph to a new file; '-' exports to stdout");
  options.registerAllowedValue("-graph-type", "max-planar");
  options.registerAllowedValue("-graph-type", "random-p3t");
  options.registerAllowedValue("-graph-type", "complete-p3t");
  options.registerAllowedValue("-graph-type", "4connected");
  options.registerAllowedValue("-graph-type", "partial-p3t-2connected");
  options.registerAllowedValue("-graph-type", "partial-p3t-connected");
  options.registerAllowedValue("-graph-type", "planar-cubic");
  options.registerAllowedValue("-graph-type", "outerplanar-max");
  options.registerAllowedValue("-graph-type", "path");
  options.registerAllowedValue("-graph-type", "star");
  options.registerAllowedValue("-graph-type", "matching");

  options.registerOption("-generate", "false", "Write a generated graph instead of a layout");
  options.registerOption("-test", "false", "Run component tests");
  cli.options(options);
}

static void processGraphs(CMDOptions& options, const LayoutCLI& cli) {
  const bool generate = options.getBool("-generate");
  const int pageBound = cli.pageBound(options);
  const int verbose = options.getInt("-verbose");
  const int n = options.getInt("-n");
  const int seed = options.getInt("-seed");
  const int graphCount = options.getInt("-graphs");
  const string graphType = options.getStr("-graph-type");
  const string inputPath = options.getStr("-i");
  string outputPath = options.getStr("-o");

  CHECK(graphCount >= 1, "-graphs must be positive");
  CHECK(!inputPath.empty() || n > 0, "generated vertex count -n must be positive");
  CHECK(inputPath.empty() || (!generate && graphCount == 1),
        "-i requires a single layout");
  if (generate) {
    CHECK(graphCount == 1, "generate writes one graph; use -graphs=1");
    if (outputPath.empty()) outputPath = "-";
  }
  CHECK(outputPath.empty() || graphCount == 1,
        "-o requires a single graph");

  auto beginAllTime = chrono::steady_clock::now();
  for (int graphIdx = 0; graphIdx < graphCount; graphIdx++) {
    auto beginTime = chrono::steady_clock::now();

    const long long nextSeed = (long long)seed + graphIdx;
    CHECK(nextSeed <= std::numeric_limits<int>::max() &&
          nextSeed >= std::numeric_limits<int>::min(),
          "seed range overflows a signed int");
    const int graphSeed = (int)nextSeed;
    Rand::setSeed(graphSeed);
    PlanarGraph graph;
    if (!inputPath.empty()) {
      const string extension = inputPath.substr(inputPath.find_last_of('.') + 1);
      if (extension == "dot") {
        graph.readDOT(inputPath);
      } else if (extension == "gml") {
        graph.readGML(inputPath);
        // Layout construction uses rotations; parsed drawing attributes are no
        // longer needed.
        graph.ioGraph.clear();
      } else {
        graph.readEdges(inputPath);
      }
    } else {
      if (graphType == "max-planar") {
        genMaxPlanar(graph, n);
      } else if (graphType == "random-p3t") {
        genRandomPlanar3Tree(graph, n);
      } else if (graphType == "complete-p3t") {
        genCompletePlanar3Tree(graph, n, verbose);
      } else if (graphType == "partial-p3t-2connected") {
        genPartialPlanar3Tree(graph, n, 0.65, 2);
      } else if (graphType == "partial-p3t-connected") {
        genPartialPlanar3Tree(graph, n, 0.65, 1);
      } else if (graphType == "planar-cubic") {
        CHECK(n % 2 == 0, "planar-cubic generator requires even n");
        genPlanarCubic(graph, n);
      } else if (graphType == "outerplanar-max") {
        genMaximalOuterplanar(graph, n);
      } else if (graphType == "path" || graphType == "star") {
        for (int i = 0; i < n; i++) graph.newVertex();
        for (int i = 1; i < n; i++) {
          const int u = graphType == "path" ? i - 1 : 0;
          Edge* edge = graph.newEdge(graph.vertices[u], graph.vertices[i]);
          Edge* last = graph.vertices[u]->edges.empty()
              ? nullptr : graph.vertices[u]->edges.back();
          graph.vertices[u]->addEdgeAfter(edge, last);
          graph.vertices[i]->addEdge(edge);
        }
      } else if (graphType == "matching") {
        for (int i = 0; i < n; i++) graph.newVertex();
        for (int i = 0; i + 1 < n; i += 2) {
          Edge* edge = graph.newEdge(graph.vertices[i], graph.vertices[i + 1]);
          graph.vertices[i]->addEdge(edge);
          graph.vertices[i + 1]->addEdge(edge);
        }
      } else {
        CHECK(graphType == "4connected");
        genPlanar4Connected(graph, n);
      }
    }
    const int generatedVertices = graph.numberOfVertices();
    const int generatedEdges = graph.numberOfEdges();
    vector<string> labels;
    for (Vertex* vertex : graph.vertices) labels.push_back(vertex->label);

    ostringstream output;
    if (generate) {
      graph.writeEdges(output);
    } else {
      vector<int> order;
      map<EdgeTy, int> edgeQueue;
      cli.build(graph, options, order, edgeQueue);
      CHECK((int)order.size() == generatedVertices &&
            (int)edgeQueue.size() == generatedEdges,
            "layout output does not cover the input graph");
      vector<vector<string>> pages(pageBound);
      vector<EdgeTy> edges;
      for (const auto& [edge, q] : edgeQueue) {
        CHECK(q >= 0 && q < pageBound, "page outside layout bound");
        pages[q].push_back("(" + labels[edge.first] + ", " + labels[edge.second] + ")");
        edges.push_back(edge);
      }
      std::cerr << "order: [";
      for (size_t i = 0; i < order.size(); i++) {
        if (i > 0) std::cerr << " ";
        std::cerr << labels[order[i]];
      }
      std::cerr << "]\n";
      for (size_t page = 0; page < pages.size(); page++) {
        std::cerr << "page " << page << ":";
        for (const string& edge : pages[page]) std::cerr << " " << edge;
        std::cerr << "\n";
      }
      cli.statistics(edges, order);
      if (!outputPath.empty()) {
        output << cli.format(options) << " " << generatedVertices << " " << generatedEdges << "\n";
        output << "order";
        for (int v : order) output << " " << v;
        output << "\n";
        for (const auto& [edge, q] : edgeQueue) {
          output << "edge " << edge.first << " " << edge.second
                 << " " << q << "\n";
        }
      }
    }
    if (!outputPath.empty()) {
      CHECK(output.good(), "failed formatting output");
      const string bytes = output.str();
      const bool standardOutput = outputPath == "-";
      const int fd = standardOutput ? STDOUT_FILENO :
          ::open(outputPath.c_str(), O_WRONLY | O_CREAT | O_EXCL, 0644);
      CHECK(fd >= 0, "cannot exclusively create output %s", outputPath.c_str());
      size_t written = 0;
      while (written < bytes.size()) {
        const ssize_t count = ::write(fd, bytes.data() + written, bytes.size() - written);
        if (count < 0 && errno == EINTR) continue;
        if (count <= 0) break;
        written += count;
      }
      const int closeStatus = standardOutput ? 0 : ::close(fd);
      CHECK(written == bytes.size() && closeStatus == 0,
            "failed writing or closing output %s", outputPath.c_str());
    }

    auto endTime = chrono::steady_clock::now();
    auto durationMs = chrono::duration_cast<chrono::milliseconds>(endTime - beginTime).count();
    LOG("processed graph %d/%d with |V| = %d, |E| = %d, seed = %d; running time is %s\n",
        graphIdx + 1, graphCount, generatedVertices, generatedEdges,
        graphSeed, ms_to_str(durationMs).c_str());
  }

  auto endAllTime = chrono::steady_clock::now();
  auto durationMs = chrono::duration_cast<chrono::milliseconds>(endAllTime - beginAllTime).count();
  if (inputPath.empty()) {
    LOG("processed %d graph(s) with requested n = %d; total running time is %s",
        graphCount, n, ms_to_str(durationMs).c_str());
  } else {
    LOG("processed input graph '%s'; total running time is %s",
        inputPath.c_str(), ms_to_str(durationMs).c_str());
  }
}

int runLayoutCLI(int argc, char* argv[], const LayoutCLI& cli) {
  auto options = CMDOptions::create();
  int returnCode = 0;

  try {
    prepareOptions(*options, cli);
    options->parse(argc, argv);
    initLogger(true);


    CHECK(!(options->getBool("-generate") && options->getBool("-test")),
          "-generate and -test cannot be combined");

    if (options->getBool("-test")) {
      CHECK(options->getStr("-i").empty() && options->getStr("-o").empty(),
            "test does not accept -i or -o");
      CHECK(bool(cli.test), "this executable has no built-in test command");
      cli.test(*options);
    } else {
      processGraphs(*options, cli);
    }
  } catch (int code) {
    returnCode = code;
  }

  return returnCode;
}
