Overview
================
BOB is a solver for constructing linear layouts of graphs, such as stack (book embeddings), queue, mixed, twist, rique, or track layouts. The tool provides two modes:

- a [SAT-based solver](#basic-setup) for building optimal layouts; it can process graphs with hundreds of vertices within several minutes;
- a collection of [fully combinatorial solvers](#combinatorial-layouts) that implement particular methods for linear graph layouts.

Visit https://spupyrev.github.io/linearlayouts.html for a survey of existing results regarding upper and lower bounds on stack number, queue number and track number of various classes of graphs. If you use BOB in your research, please cite it as follows:

    @misc{bob,
      author       = {Pupyrev, Sergey},
      title        = {A {SAT}-based solver for constructing optimal linear layouts of graphs},
      howpublished = {\url{https://github.com/spupyrev/bob}},
      year         = {2017},
      note         = {Accessed: today's date}
    }

Basic Setup
--------

1. Build the executable by running:

        make

2. Solve a layout instance:

        ./build/bob -i=graphs/graph.dot -stacks=3

    The embedded SAT solver tests embeddability and prints the resulting layout. The tool accepts graphs in the [DOT](https://en.wikipedia.org/wiki/DOT_(graph_description_language)) and [GML](https://en.wikipedia.org/wiki/Graph_Modelling_Language) formats. For the list of supported options use:

        ./build/bob -help

Run the lightweight solver tests with:

        make test

To use an external solver instead, export the model in [DIMACS](http://www.satcompetition.org/2009/format-benchmarks2009.html) format:

        ./build/bob -i=graphs/graph.dot -o=graph.dimacs -stacks=3

        treengeling graph.dimacs > result.dimacs

        ./build/bob -i=graphs/graph.dot -result=result.dimacs -stacks=3

Linear Layout Modes
--------

| Type | Option | Description | Reference |
| --- | --- | --- | --- |
| Stack | `-stacks=k` | Each page forbids crossings | [Book embedding](https://en.wikipedia.org/wiki/Book_embedding) |
| Queue | `-queues=k` | Each page forbids nestings | [Queue number](https://en.wikipedia.org/wiki/Queue_number) |
| Mixed | `-stacks=s -queues=q` | Uses both stack and queue pages | [The mixed page number of graphs](https://doi.org/10.1016/j.tcs.2022.07.036) |
| Twist | `-twists=k` | Allows at most `k` pairwise crossing edges | — |
| Rique | `-riques=k` | Uses restricted-input deque pages | [The Rique-Number of Graphs](https://doi.org/10.1007/978-3-031-22203-0_27) |

Examples
--------

Test whether an input graph can be embedded in 2 [stacks](https://spupyrev.github.io/linearlayouts.html#stack)

        ./build/bob -i=graphs/graph.dot -stacks=2


Test whether an input graph can be embedded in 2 [queues](https://spupyrev.github.io/linearlayouts.html#queue)

        ./build/bob -i=graphs/graph.dot -queues=2

Test whether an input graph admits a [6-track layout](https://spupyrev.github.io/linearlayouts.html#track) and print resulting layout

        ./build/bob -i=graphs/weakly_6tracks.gml -tracks=6

Combinatorial Layouts
--------

The planar queue-layout solver implements the product structure algorithm [Planar Graphs Have Bounded Queue-Number](https://doi.org/10.1145/3385731) (JACM, 2020), and its improvement for the 33-queue layout. Build with `make planar_queues`, then choose 49 or 33 queues:

        ./build/planar_queues -i=graphs/planar20.edges -queues=<49|33> -o=graph.layout

License
--------
BOB is released under the [MIT License](LICENSE).
