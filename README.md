Book Embedding
================
BE is a tool for constructing optimal linear layouts of graphs. With a modern SAT solver, it is capable to compute optimal layouts of graphs with hundreds of vertices within several minutes.

Visit http://be.cs.arizona.edu for an interactive demo.

Basic Setup
--------

1. Compile the library by running:

        make

2. Run the tool:

        ./be -i=graph.dot -o=graph.dimacs -type=stack -pages=2 -verbose=true

    The tool accepts graphs in the [DOT](https://en.wikipedia.org/wiki/DOT_(graph_description_language)) and [GML](https://en.wikipedia.org/wiki/Graph_Modelling_Language) formats. The output is the [DIMACS](http://www.satcompetition.org/2009/format-benchmarks2009.html) format.
For the list of supported options use:

        ./be -help
	
3. Download and setup a SAT solver such as [Lingeling](http://fmv.jku.at/lingeling) or [Glucose](http://www.labri.fr/perso/lsimon/glucose) 

4. Use the SAT solver to test embeddability of the graph:

        ./treengeling graph.dimacs

License
--------
Code is released under the [MIT License](MIT-LICENSE.txt).
