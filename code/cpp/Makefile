# Solver-free dominance relaxation (see dominance.cpp). `make` builds ./build/dominance.
CXX ?= c++
CXXFLAGS ?= -O2 -std=c++17 -Wall -Wextra

build/dominance: dominance.cpp
	mkdir -p build
	$(CXX) $(CXXFLAGS) -o $@ $<

clean:
	rm -rf build

.PHONY: clean
