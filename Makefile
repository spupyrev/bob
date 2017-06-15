# Variables
CXX = g++
CXXFLAGS = -Isrc -Wall -Wno-unknown-pragmas -O3 -std=c++11

HEADERS = $(wildcard **/*.h)

SOURCES = $(wildcard src/*.cpp)

# Targets
TARGET = be

OBJECTS = $(SOURCES:src/%.cpp=build/%.o)

## Default rule executed
all: $(TARGET)
	@true

## Clean Rule
clean:
	$(RM) $(TARGET) $(OBJECTS)

noomp: $(TARGET)
	@true

## Rule for making the actual target
$(TARGET): $(OBJECTS)
	@echo "Linking object files to target $@..."
	$(CXX) $(LDFLAGS) -o $@ $^
	@echo "-- Link finished --"

## Generic compilation rule for object files from cpp files
build/%.o : src/%.cpp $(HEADERS) Makefile
	@mkdir -p $(dir $@)
	$(CXX) $(CXXFLAGS) -c $< -o $@
