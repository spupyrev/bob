#include "logging.h"
#include "glucoseMain.h"
#include "cmd_options.h"
#include "io_graph.h"
#include "graph_parser.h"

using namespace std;

void prepareCMDOptions(int argc, char** argv, CMDOptions& args) {
	string msg;
	msg += "Usage: bob [options]\n";
	args.SetUsageMessage(msg);

	args.AddAllowedOption("-i", "", "Input file name (stdin, if no input file is supplied)");
  args.AddAllowedOption("-o", "", "Output file name (stdout, if no output file is supplied)");
  args.AddAllowedOption("-result", "", "Resulting assignment in Dimacs format");

  args.AddAllowedOption("-stacks", "0", "The number of stacks to use");
  args.AddAllowedOption("-queues", "0", "The number of queues to use");
  args.AddAllowedOption("-tracks", "0", "The number of tracks to use");

	args.AddAllowedOption("-trees", "false", "Whether every page is a tree");
	args.AddAllowedOption("-dispersible", "false", "Whether every page is a matching");
	args.AddAllowedOption("-directed", "false", "Whether the input graph is directed");

  args.AddAllowedOption("-verbose", "0", "Verbose debug output");

	args.Parse(argc, argv);
}

void process(const CMDOptions& options) {
	// input
	IOGraph graph;
	GraphParser parser;
	if (!parser.readGraph(options.getOption("-i"), graph)) {
		string file = options.getOption("-i");
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

  // prepare params
  Params params;
 	params.trees = options.getBool("-trees");
  params.dispersible = options.getBool("-dispersible");
  params.directed = options.getBool("-directed");
  params.verbose = options.getInt("-verbose");
  params.stacks = options.getInt("-stacks");
  params.queues = options.getInt("-queues");
  params.tracks = options.getInt("-tracks");
  CHECK(params.stacks + params.queues + params.tracks > 0, "missing page number");

  if (params.tracks > 0) {
    CHECK(params.stacks == 0 && params.queues == 0, "cannot mix track and stack/queue layouts");
    params.stacks = 1;
    params.embedding = TRACK;
  } else if (params.stacks > 0 && params.queues > 0) {
    params.embedding = MIXED;
  } else if (params.stacks > 0) {
    params.embedding = STACK;
  } else if (params.queues > 0) {
    params.embedding = QUEUE;
  } else {
    ERROR("unknown type of layout");
  }

  params.modelFile = options.getOption("-o");
  params.resultFile = options.getOption("-result");

  CHECK(params.modelFile == "" || params.resultFile == "", "only one of ['-o', '-result'] can be provided");

  if (params.verbose) {
    if (params.isStack() || params.isQueue() || params.isMixed()) {
      string ps = params.isStack() ? "stacks" : params.isQueue() ? "queues" : "stack+queue";
      LOG("processing graph with %d vertices and %d edges on %d %s with params: %s", inputGraph.nc, inputGraph.edges.size(), params.stacks + params.queues, ps.c_str(), params.toString().c_str());
    } else if (params.isTrack()) {
      LOG("processing graph with %d vertices and %d edges on %d tracks with params: %s", inputGraph.nc, inputGraph.edges.size(), params.tracks, params.toString().c_str());
    }
  }

	bool res = run(inputGraph, params);
	if (!res) {
		LOG("layout does not exist");
	}
}

int main(int argc, char *argv[]) {
	auto options = CMDOptions::Create();

	int returnCode = 0;
	try {
		prepareCMDOptions(argc, argv, *options);
		process(*options);
	}	catch (int code) {
		returnCode = code;
	}

	return returnCode;
}
