# Variables
CXX = g++
CXXFLAGS = -Isrc -Wall -std=c++11 -O3 -g
LDFLAGS = -Wall -lz -g

HEADERS = $(wildcard **/*.h)

SOURCES = $(wildcard src/*.cpp)

# Targets
TARGET = bob

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
	$(CXX) $^ $(LDFLAGS) -o $@
	@echo "-- Link finished --"

## Generic compilation rule for object files from cpp files
build/%.o : src/%.cpp $(HEADERS) Makefile
	@mkdir -p $(dir $@)
	$(CXX) $(CXXFLAGS) -c $< -o $@
