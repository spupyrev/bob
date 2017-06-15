#include "logging.h"
#include "glucoseMain.h"
#include "cmd_options.h"
#include "dot_graph.h"

using namespace std;

void prepareCMDOptions(int argc, char** argv, CMDOptions& args) {
	string msg;
	msg += "Usage: be [options]\n";
	args.SetUsageMessage(msg);

	args.AddAllowedOption("-i", "", "Input file name (stdin, if no input file is supplied)");
	args.AddAllowedOption("-o", "", "Output file name (stdout, if no output file is supplied)");

	args.AddAllowedOption("-type", "stack", "Type of layout");
	args.AddAllowedValue("-type", "stack");
	args.AddAllowedValue("-type", "queue");
	args.AddAllowedValue("-type", "mixed");

	args.AddAllowedOption("-pages", "The number of pages");
	args.AddAllowedOption("-trees", "false", "Whether every page is a tree");
	args.AddAllowedOption("-dispersible", "false", "Whether every page is a matching");

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

  // prepare params
  Params params;
  string type = options.getOption("-type");
  if (type == "stack") {
    params.embedding = STACK;
  } else if (type == "queue") {
    params.embedding = QUEUE;
  } else if (type == "mixed") {
    params.embedding = MIXED;
  } else {
    ERROR("unknown embedding type");
  }
  params.pages = options.getInt("-pages");
 	params.trees = options.getBool("-trees");
  params.dispersible = options.getBool("-dispersible");
  params.verb = options.getBool("-verbose");
  params.modelFile = options.getOption("-o");

  LOG_IF(params.verb, "processing graph with %d vertices and %d edges", inputGraph.nc, inputGraph.edges.size());
  LOG_IF(params.verb, "[type = %s, pages = %d, trees = %d, dispersible = %d]", type.c_str(), params.pages, params.trees, params.dispersible);

	bool res = run(inputGraph, params);
	if (!res) {
		LOG("embedding with %d pages does not exist", params.pages);
	}
}

int main(int argc, char *argv[]) {
	auto options = CMDOptions::Create();

	int returnCode = 0;
	try
	{
		prepareCMDOptions(argc, argv, *options);
		processGraph(*options);
	}
	catch (int code)
	{
		returnCode = code;
		LOG("exit code: %d", returnCode);
	}

	return returnCode;
}
