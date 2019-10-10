#pragma once

#include <iostream>
#include <fstream>
#include <sstream>
#include <string>
#include <vector>
#include <map>
#include <cassert>
#include <functional>

using namespace std;

class Attr {
//private:
public:
	map<string, string> attr;

public:
	string getAttr(const string& key)	{
		if (attr.count(key) == 0) {
			cerr << "attribute '" << key << "' not found" << "\n";
		}
		assert(attr.find(key) != attr.end());
		return attr[key];
	}

	double getDoubleAttr(const string& key)	{
		string value = getAttr(key);
		double n;
		istringstream (value) >> n;
		return n;
	}

	void setAttr(const string& key, const string& value) {
		attr[key] = value;
	}

	void setAttr(const map<string, string>& attr_) {
		attr = attr_;
	}

	bool hasAttr(const string& key)	{
		return (attr.find(key) != attr.end());
	}

	void removeAttr(const string& key) {
		if (attr.find(key) != attr.end())
			attr.erase(attr.find(key));
	}
};

class DotNode : public Attr
{
private:
	DotNode(const DotNode&);
	DotNode& operator = (const DotNode&);

public:
	int index;
	string id;

	DotNode(int index, const string& id): index(index), id(id) {}
};

class DotEdge : public Attr
{
private:
	DotEdge(const DotEdge&);
	DotEdge& operator = (const DotEdge&);

public:
	int index;
	string source;
	string target;

	DotEdge(int index, const string& source, const string& target): index(index), source(source), target(target) {}
};

class DotGraph
{
private:
	bool initialized;

public:
	DotGraph(): initialized(false) {}
	~DotGraph() {
		clear();
	}

	void clear() {
		for (auto& o : style) {
			delete o;
		}
		for (auto& o : nodes) {
			delete o;
		}
		for (auto& o : edges) {
			delete o;
		}
		initialized = false;
		style.clear();
		nodes.clear();
		edges.clear();
		adj.clear();
		adjE.clear();
		idToNode.clear();
	}

	void clear2() {
		initialized = false;
		style.clear();
		nodes.clear();
		edges.clear();
		adj.clear();
		adjE.clear();
		idToNode.clear();
	}

	vector<DotNode*> style;
	vector<DotNode*> nodes;
	vector<DotEdge*> edges;

	vector<vector<int> > adj;
	vector<vector<int> > adjE;

	map<string, DotNode*> idToNode;

	DotNode* addNode(const string& id) {
		assert(getNode(id) == nullptr);

		auto node = new DotNode(nodes.size(), id);
		nodes.push_back(node);
		idToNode[id] = node;
		return node;
	}

	DotEdge* addEdge(const string& source, const string& target) {
		assert(getNode(source, true) != nullptr);
		assert(getNode(target, true) != nullptr);
		auto edge = new DotEdge(edges.size(), source, target);
		edges.push_back(edge);
		return edge;
	}

	DotNode* getNode(const string& id, bool create = false) {
		if (idToNode.find(id) == idToNode.end()) {
			if (create) return addNode(id);
			return nullptr;
		}
		return idToNode[id];
	}

	void initAdjacencyList()
	{
		if (initialized) return;

		adj = vector<vector<int> >(nodes.size(), vector<int>());
		adjE = vector<vector<int> >(nodes.size(), vector<int>());
		for (size_t i = 0; i < edges.size(); i++)
		{
			DotNode* s = getNode(edges[i]->source);
			DotNode* t = getNode(edges[i]->target);

			adj[s->index].push_back(t->index);
			adjE[s->index].push_back(i);
			adj[t->index].push_back(s->index);
			adjE[t->index].push_back(i);
		}

		initialized = true;
	}
};

class DotParser {
	DotParser(const DotParser&);
	DotParser& operator = (const DotParser&);

public:
	DotParser() {}

	bool readGraph(const string& filename, DotGraph& graph) const {
		auto func = static_cast<bool (DotParser::*)(istream&, DotGraph&) const>(&DotParser::readGraph);
		return wrapRead(func, filename, graph);
	}
	bool readGraph(istream& in, DotGraph& graph) const {
		std::stringstream input;
		input << in.rdbuf();

		input.clear();
		input.seekg(0, std::ios::beg);

		graph.clear();
		bool res = readDotGraph(input, graph);
		//cerr << "parsing DOT graph: " << (res ? "ok" : "failed") << "\n";
		if (res) return true;

		input.clear();
		input.seekg(0, std::ios::beg);

		graph.clear();
		res = readGmlGraph(input, graph);
		//cerr << "parsing GML graph: " << (res ? "ok" : "failed") << "\n";
		if (res) return true;

		return false;
	}

	bool readDotGraph(const string& filename, DotGraph& graph) const {
		auto func = static_cast<bool (DotParser::*)(istream&, DotGraph&) const>(&DotParser::readDotGraph);
		return wrapRead(func, filename, graph);
	}
	bool readDotGraph(istream& in, DotGraph& graph) const;

	bool readGmlGraph(const string& filename, DotGraph& graph) const {
		auto func = static_cast<bool (DotParser::*)(istream&, DotGraph&) const>(&DotParser::readGmlGraph);
		return wrapRead(func, filename, graph);
	}
	bool readGmlGraph(istream& in, DotGraph& graph) const;

	bool writeDotGraph(const string& filename, DotGraph& graph) const {
		auto func = static_cast<bool (DotParser::*)(ostream&, DotGraph&) const>(&DotParser::writeDotGraph);
		return wrapWrite(func, filename, graph);
	}
	bool writeDotGraph(ostream& out, DotGraph& graph) const;

	bool writeGmlGraph(const string& filename, DotGraph& graph) const {
		auto func = static_cast<bool (DotParser::*)(ostream&, DotGraph&) const>(&DotParser::writeGmlGraph);
		return wrapWrite(func, filename, graph);
	}
	bool writeGmlGraph(ostream& out, DotGraph& graph) const;

private:
	void checkFile(const string& filename) const {
		if (filename != "") {
			ifstream fileStream;
			fileStream.open(filename.c_str(), ios::in);
			if (!fileStream) {
				cerr << "input file '" << filename << "' doesn't exist\n";
				throw 20;
			}
			fileStream.close();
		}
	}

	bool wrapRead(std::function<bool(const DotParser&, istream&, DotGraph&)> func, const string& filename, DotGraph& graph) const {
		checkFile(filename);

		if (filename != "") {
			ifstream fileStream;
			fileStream.open(filename.c_str(), ios::in);
			bool result = func(*this, fileStream, graph);
			fileStream.close();
			return result;
		} else {
			return func(*this, cin, graph);
		}
	}

	bool wrapWrite(std::function<bool(const DotParser&, ostream&, DotGraph&)> func, const string& filename, DotGraph& graph) const {
		if (filename != "")	{
			ofstream fileStream;
			fileStream.open(filename.c_str(), ios::out);
			bool result = func(*this, fileStream, graph);
			fileStream.close();
			return result;
		} else {
			return func(*this, cout, graph);
		}
	}
};
