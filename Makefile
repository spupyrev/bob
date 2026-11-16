CXX ?= g++

CPPFLAGS += -Isrc
CXXFLAGS += -Wall -Wextra -Wno-unused-parameter -std=c++17 -pthread
LDLIBS += -lz -pthread

TARGET := build/bob
DEBUG_TARGET := build/bob_debug
GRAPH_TEST_TARGET := build/test_graph_algorithms
PLANAR_TARGET := build/planar_queues
PLANAR_SOURCES := src/combinatorial/planar_queues.cpp \
                  src/combinatorial/layout_cli.cpp \
                  src/combinatorial/layered_h_partition.cpp \
                  src/combinatorial/queue_orders.cpp \
                  src/combinatorial/augmentation.cpp \
                  src/combinatorial/planar_graph.cpp \
                  src/combinatorial/planar_graph_io.cpp \
                  src/combinatorial/planarity.cpp \
                  src/combinatorial/graph_generator.cpp \
                  src/combinatorial/tests.cpp \
                  src/bob/common.cpp src/bob/graph_algorithms.cpp src/bob/queues.cpp \
                  src/bob/dot_parser.cpp src/bob/gml_parser.cpp
PLANAR_OBJECTS := $(PLANAR_SOURCES:src/%.cpp=build/obj/%.o)

SOURCES := $(wildcard src/bob/*.cpp) $(wildcard src/glucose/*.cpp) \
           $(wildcard src/satsuma/*.cpp)
OBJECTS := $(SOURCES:src/%.cpp=build/obj/%.o)
DEBUG_OBJECTS := $(SOURCES:src/%.cpp=build/debug/%.o)
DEPFILES := $(OBJECTS:.o=.d) $(DEBUG_OBJECTS:.o=.d) $(PLANAR_OBJECTS:.o=.d) $(GRAPH_TEST_TARGET).d

.PHONY: all debug d test clean planar_queues test-planar-queues
.DEFAULT_GOAL := all

all: $(TARGET)
planar_queues: $(PLANAR_TARGET)
test-planar-queues: $(PLANAR_TARGET)
	python3 tests/test_planar_queues.py --vertices=100 --graphs=10
	python3 tests/test_planar_dot.py --binary ./$(PLANAR_TARGET) --mode queues
debug d: $(DEBUG_TARGET)
test: $(TARGET) $(GRAPH_TEST_TARGET)
	./$(GRAPH_TEST_TARGET)
	./tests/run_tests.sh ./$(TARGET)

$(TARGET): $(OBJECTS)
	@echo "Linking $@"
	$(CXX) $^ $(LDFLAGS) $(LDLIBS) -o $@

$(GRAPH_TEST_TARGET): tests/test_graph_algorithms.cpp build/obj/bob/graph_algorithms.o
	@mkdir -p $(@D)
	$(CXX) $(CPPFLAGS) $(CXXFLAGS) -MMD -MP -MF $@.d $< build/obj/bob/graph_algorithms.o $(LDFLAGS) -o $@

$(PLANAR_TARGET): $(PLANAR_OBJECTS)
	@echo "Linking $@"
	$(CXX) $^ $(LDFLAGS) -o $@

$(DEBUG_TARGET): $(DEBUG_OBJECTS)
	@echo "Linking $@"
	$(CXX) $^ $(LDFLAGS) $(LDLIBS) -o $@

build/obj/%.o: CXXFLAGS += -O3 -g
build/debug/%.o: CXXFLAGS += -O0 -g3 -DDEBUG

build/obj/%.o build/debug/%.o: src/%.cpp Makefile
	@mkdir -p $(@D)
	@echo "Compiling $<"
	$(CXX) $(CPPFLAGS) $(CXXFLAGS) -MMD -MP -c $< -o $@

clean:
	$(RM) -r build

-include $(DEPFILES)
