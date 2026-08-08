CXX ?= g++

CPPFLAGS += -Isrc
CXXFLAGS += -Wall -Wextra -Wno-unused-parameter -std=c++17 -pthread
LDLIBS += -lz -pthread

TARGET := build/bob
DEBUG_TARGET := build/bob_debug

SOURCES := $(wildcard src/bob/*.cpp) $(wildcard src/glucose/*.cpp)
OBJECTS := $(SOURCES:src/%.cpp=build/obj/%.o)
DEBUG_OBJECTS := $(SOURCES:src/%.cpp=build/debug/%.o)
DEPFILES := $(OBJECTS:.o=.d) $(DEBUG_OBJECTS:.o=.d)

.PHONY: all debug d test clean
.DEFAULT_GOAL := all

all: $(TARGET)
debug d: $(DEBUG_TARGET)
test: $(TARGET)
	./tests/run_tests.sh ./$(TARGET)

$(TARGET): $(OBJECTS)
	@echo "Linking $@"
	$(CXX) $^ $(LDFLAGS) $(LDLIBS) -o $@

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
