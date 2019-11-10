Overview
================
BOB is a SAT-based tool for constructing optimal linear layouts of graphs. With a modern SAT solver, it is capable to compute optimal stack, queue, or track layouts of graphs with hundreds of vertices within several minutes.

Visit http://be.cs.arizona.edu for an interactive demo or https://spupyrev.github.io/linearlayouts.html for a survey of existing results regarding upper and lower bounds on stack number, queue number and track number of various classes of graphs.

Basic Setup
--------

1. Compile the library by running:

        make

2. Run the tool:

        bob -i=graphs/graph.dot -o=graph.dimacs -stacks=3

    The tool accepts graphs in the [DOT](https://en.wikipedia.org/wiki/DOT_(graph_description_language)) and [GML](https://en.wikipedia.org/wiki/Graph_Modelling_Language) formats. The output is the [DIMACS](http://www.satcompetition.org/2009/format-benchmarks2009.html) format.
For the list of supported options use:

        bob -help
	
3. Download and setup a SAT solver such as [Lingeling](http://fmv.jku.at/lingeling) or [Glucose](http://www.labri.fr/perso/lsimon/glucose) 

4. Use the SAT solver to test embeddability of the graph:

        treengeling graph.dimacs > result.dimacs

5. Print the resulting layout:

        bob -i=graphs/graph.dot -result=result.dimacs -stacks=3

Examples
--------

Test whether an input graph can be embedded in 2 [stacks](https://spupyrev.github.io/linearlayouts.html#stack)

        bob -i=graphs/graph.dot -o=graph.dimacs -stacks=2


Test whether an input graph can be embedded in 2 [queues](https://spupyrev.github.io/linearlayouts.html#queue)

        bob -i=graphs/graph.dot -o=graph.dimacs -queues=2

Test whether an input graph admits a [6-track layout](https://spupyrev.github.io/linearlayouts.html#track) and print resulting layout

        bob -i=graphs/weakly_6tracks.gml -o=graph.dimacs -tracks=6
        treengeling graph.dimacs > result.dimacs
        bob -i=graphs/weakly_6tracks.gml -result=result.dimacs -tracks=6

License
--------
Code is released under the [MIT License](MIT-LICENSE.txt).
