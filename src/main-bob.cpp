#include "logging.h"
#include "glucoseMain.h"
#include "cmd_options.h"
#include "dot_graph.h"

using namespace std;

void prepareCMDOptions(int argc, char** argv, CMDOptions& args) {
	string msg;
	msg += "Usage: bob [options]\n";
	args.SetUsageMessage(msg);

	args.AddAllowedOption("-i", "", "Input file name (stdin, if no input file is supplied)");
	args.AddAllowedOption("-o", "", "Output file name (stdout, if no output file is supplied)");

  args.AddAllowedOption("-stacks", "0", "The number of stacks to use");
  args.AddAllowedOption("-queues", "0", "The number of queues to use");
  args.AddAllowedOption("-tracks", "0", "The number of tracks to use");

	args.AddAllowedOption("-trees", "false", "Enfore every page to be a tree");
	args.AddAllowedOption("-dispersible", "false", "Enfore every page to be a matching");

	args.AddAllowedOption("-verbose", "true", "Verbose debug output");

	args.Parse(argc, argv);
}

void processGraph(const CMDOptions& options) {
	// input
	DotGraph graph;
	DotParser parser;
	if (!parser.readGraph(options.getOption("-i"), graph)) {
		string file = options.getOption("-i");
		if (file.length() == 0) file = "stdin";
		ERROR("cannot parse input graph from '" + file + "'");
	}

  // create graph
  InputGraph inputGraph;
  inputGraph.nc = graph.nodes.size();
  for (size_t i = 0; i < graph.edges.size(); i++) {
  	auto s = graph.getNode(graph.edges[i]->source);
  	auto t = graph.getNode(graph.edges[i]->target);

  	if (s->index < t->index) {
	    inputGraph.edges.push_back(make_pair(s->index, t->index));
	  } else if (s->index > t->index) {
	    inputGraph.edges.push_back(make_pair(t->index, s->index));
	  }
  }

  // fill params
  Params params;
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
    ERROR("unknown embedding type");
  }

 	params.trees = options.getBool("-trees");
  params.dispersible = options.getBool("-dispersible");
  params.verbose = options.getBool("-verbose") ? 1 : 0;
  params.modelFile = options.getOption("-o");

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
		LOG("embedding does not exist");
	}
}

int main(int argc, char *argv[]) {
	auto options = CMDOptions::Create();

	int returnCode = 0;
	try	{
		prepareCMDOptions(argc, argv, *options);
		processGraph(*options);
	} catch (int code) {
		returnCode = code;
	}

	return returnCode;
}