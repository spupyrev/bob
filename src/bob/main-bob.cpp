#include "logging.h"
#include "glucoseMain.h"
#include "cmd_options.h"
#include "io_graph.h"
#include "graph_parser.h"
#include "sat_utils.h"
#include "stats.h"

#include <algorithm>

using namespace std;

void prepareCMDOptions(int argc, char** argv, CMDOptions& args) {
	string msg;
	msg += "Usage: bob [options]\n";
	args.setUsageMessage(msg);

	args.registerOption("-i", "", "Input file name (stdin, if no input file is supplied)");
  args.registerOption("-o", "", "Output file name (stdout, if no output file is supplied)");
  args.registerOption("-result", "", "Resulting assignment in Dimacs format");
  args.registerOption("-stats", "false", "Print basic graph statistics and exit");

  args.registerOption("-stacks", "0", "The number of stacks to use");
  args.registerOption("-queues", "0", "The number of queues to use");
  args.registerOption("-twists", "0", "The maximum size of a twist");
  args.registerOption("-tracks", "0", "The number of tracks to use");
  args.registerOption("-mixed-pages", "0", "The number of pages whose type is chosen by SAT");
  args.registerOption("-riques", "0", "The number of restricted-input deque pages");

	args.registerOption("-constraints", "", "Semicolon-separated general constraints");
	args.registerOption("-satsuma", "false", "Whether to apply Satsuma symmetry detection");
	args.registerOption("-basic-symmetry", "true", "Whether to apply built-in symmetry breaking");
  args.registerOption("-multi", "false", "Allow edges on multiple pages");
  args.registerOption("-fixedOrder", "false", "Use the input vertex order as a fixed order");
  args.registerOption("-node-rel", "", "Semicolon-separated partial vertex orders by label");
  args.registerOption("-edge-pages", "", "Admissible pages for labeled edges");
  args.registerOption("-timeout", "0", "Maximum embedded-solver time in seconds (0 means unlimited)");
  args.registerOption("-check", "true", "Verify every constructed layout");
  args.registerOption("-adjacent", "false", "Keep edges at adjacent vertices on the same page");
  args.registerOption("-local", "0", "Maximum number of pages incident to a vertex");
  args.registerOption("-strict", "false", "Enforce strict queue layouts");
  args.registerOption("-span", "0", "Maximum edge span for track layouts");

  args.registerOption("-verbose", "0", "Verbose debug output");

	args.parse(argc, argv);
}

void printResult(const InputGraph& inputGraph, const Params& params, const Result& result) {
  std::cerr << "order: [";
  for (size_t i = 0; i < result.order.size(); i++) {
    if (i > 0) std::cerr << " ";
    std::cerr << inputGraph.getVertexLabel(result.order[i]);
  }
  std::cerr << "]\n";

  for (int page = 0; page < params.page_var_num(); page++) {
    std::cerr << "page " << page << ":";
    for (size_t edge = 0; edge < inputGraph.edges.size(); edge++) {
      if (result.isOnPage(edge, page))
        std::cerr << " " << inputGraph.edge_to_string(edge);
    }
    std::cerr << "\n";
  }

  if (params.isTrack()) {
    for (int track = 0; track < params.tracks; track++) {
      std::cerr << "track " << track << ":";
      for (int vertex : result.order) {
        if (result.tracks[vertex] == track)
          std::cerr << " " << inputGraph.getVertexLabel(vertex);
      }
      std::cerr << "\n";
    }
  }

  printLayoutStatistics(std::cerr, inputGraph, params, result);
}

void process(const CMDOptions& options) {
	// input
	IOGraph graph;
	GraphParser parser;
	if (!parser.readGraph(options.getStr("-i"), graph)) {
		string file = options.getStr("-i");
		if (file.length() == 0) file = "stdin";
		ERROR("cannot parse input graph from '" + file + "'");
	}

  // create graph
  InputGraph inputGraph;
  inputGraph.nc = (int)graph.nodes.size();
  for (int i = 0; i < inputGraph.nc; i++) {
    inputGraph.id2label[i] = graph.nodes[i].id;
    inputGraph.label2id[graph.nodes[i].id] = i;
  }
  for (size_t i = 0; i < graph.edges.size(); i++) {
  	auto s = graph.getNode(graph.edges[i].source);
  	auto t = graph.getNode(graph.edges[i].target);
  	CHECK(s->index != t->index, "Self-edges are not supported");

  	if (s->index < t->index) {
	    inputGraph.edges.push_back(make_pair(s->index, t->index));
	    inputGraph.direction.push_back(true);
	  } else {
	    inputGraph.edges.push_back(make_pair(t->index, s->index));
	    inputGraph.direction.push_back(false);
	  }
  }

  if (options.getBool("-stats")) {
    printStats(inputGraph.nc, inputGraph.edges);
    return;
  }

  // prepare params
  Params params;
  params.constraints = SplitNotNull(options.getStr("-constraints"), ";");
  params.applySatsuma = options.getBool("-satsuma");
  params.verbose = options.getInt("-verbose");
  params.stacks = options.getInt("-stacks");
  params.queues = options.getInt("-queues");
  params.twists = options.getInt("-twists");
  params.tracks = options.getInt("-tracks");
  params.mixedPages = options.getInt("-mixed-pages");
  params.riques = options.getInt("-riques");
  CHECK(params.stacks >= 0 && params.queues >= 0 && params.twists >= 0 &&
        params.tracks >= 0 && params.mixedPages >= 0 && params.riques >= 0,
        "layout counts must be non-negative");
  CHECK(params.page_num() > 0, "missing page number");

  if (params.riques > 0) {
    CHECK(params.stacks == 0 && params.queues == 0 && params.twists == 0 &&
          params.tracks == 0 && params.mixedPages == 0,
          "rique layouts cannot be mixed with other layouts");
    params.embedding = RIQUE;
  } else if (params.tracks > 0) {
    CHECK(params.stacks == 0 && params.queues == 0 && params.twists == 0 &&
          params.mixedPages == 0 && params.riques == 0,
          "cannot mix track and other layouts");
    params.stacks = 1;
    params.embedding = TRACK;
  } else if (params.twists > 0) {
    CHECK(params.stacks == 0 && params.queues == 0 && params.mixedPages == 0,
          "cannot mix twists and page layouts");
    params.embedding = TWIST;
  } else if (params.mixedPages > 0) {
    CHECK(params.stacks == 0 && params.queues == 0,
          "mixed pages cannot be combined with fixed page types");
    params.embedding = MIXED_PAGES;
  } else if (params.stacks > 0 && params.queues > 0) {
    params.embedding = MIXED;
  } else if (params.stacks > 0) {
    params.embedding = STACK;
  } else if (params.queues > 0) {
    params.embedding = QUEUE;
  } else {
    ERROR("unknown type of layout");
  }

  params.applyBasicSymmetry = options.getBool("-basic-symmetry");
  params.fixedOrder = options.getBool("-fixedOrder");
  const int timeoutSeconds = options.getInt("-timeout");
  params.adjacent = options.getBool("-adjacent");
  params.local = options.getInt("-local");
  sort_unique(params.constraints);
  params.strict = options.getBool("-strict");
  params.span = options.getInt("-span");
  CHECK(timeoutSeconds >= 0, "timeout must be non-negative");
  CHECK(params.local >= 0, "local page bound must be non-negative");
  CHECK(params.span >= 0, "track span must be non-negative");
  CHECK(!params.strict || params.isQueue(), "strict layouts require queues");
  CHECK(params.span == 0 || params.isTrack(), "span is only valid for track layouts");
  CHECK(!params.fixedOrder || !params.isTrack(),
        "fixed-order track layouts are not implemented");
  CHECK(!contains(params.constraints, "trees") || params.stacks + params.queues > 0,
        "tree constraints require stack or queue pages");
  CHECK(params.local == 0 || params.stacks + params.queues > 0,
        "local constraints require stack or queue pages");
  CHECK(!contains(params.constraints, "dispersable") || params.page_var_num() > 0,
        "dispersible constraints require page variables");

  const bool multiPage = options.getBool("-multi");
  CHECK(!multiPage || params.page_var_num() > 0,
        "multi-page edges require page variables");
  if (multiPage)
    inputGraph.multiPage.assign(inputGraph.edges.size(), true);
  if (params.fixedOrder)
    inputGraph.setNodeOrder(identity(inputGraph.nc));
  applyNodeRelOption(inputGraph, options.getStr("-node-rel"));
  applyEdgePagesOption(inputGraph, options.getStr("-edge-pages"));
  CHECK(inputGraph.edgePages.empty() || params.page_var_num() > 0,
        "edge-page constraints require page variables");
  CHECK(!params.fixedOrder || inputGraph.nodeRel.empty(),
        "node-rel cannot be combined with fixedOrder");

  params.modelFile = options.getStr("-o");
  params.resultFile = options.getStr("-result");

  CHECK(params.modelFile == "" || params.resultFile == "", "only one of ['-o', '-result'] can be provided");

  if (params.verbose) {
    if (params.isStack() || params.isQueue() || params.isMixed()) {
      string ps = params.isStack() ? "stacks" : params.isQueue() ? "queues" : "stack+queue";
      LOG("processing graph with %d vertices and %d edges on %d %s with params: %s", inputGraph.nc, inputGraph.edges.size(), params.stacks + params.queues, ps.c_str(), params.to_string().c_str());
    } else if (params.isTrack()) {
      LOG("processing graph with %d vertices and %d edges on %d tracks with params: %s", inputGraph.nc, inputGraph.edges.size(), params.tracks, params.to_string().c_str());
    }
  }

	Result result = runWithTimeout(inputGraph, params, timeoutSeconds);
	if (result.isSat()) {
    if (options.getBool("-check"))
      CHECK(checkSAT(inputGraph, params, result), "constructed layout is invalid");
    printResult(inputGraph, params, result);
  } else if (result.isUnsat()) {
		LOG("layout does not exist");
  } else if (result.isTimeout()) {
    LOG("time limit exceeded");
  } else {
    ERROR("SAT solver failed");
  }
}

int main(int argc, char *argv[]) {
	auto options = CMDOptions::create();

	int returnCode = 0;
	try {
		prepareCMDOptions(argc, argv, *options);
		process(*options);
	}	catch (int code) {
		returnCode = code;
	}

	return returnCode;
}
