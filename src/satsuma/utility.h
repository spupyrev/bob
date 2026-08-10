#pragma once

#include <iostream>
#include <algorithm>
#include <random>
#include <unordered_map>
#include <unordered_set>
#include <fstream>
#include <set>
#include <cstring>
#include <queue>
#include <memory>
#include <chrono>
#include <iomanip>

int sat_to_graph(int l) {
    return 2*(abs(l)-1) + (l < 0);
}

int graph_to_sat(int vertex) {
    const bool is_neg = vertex % 2;
    int variable = floor(vertex/2) + 1;
    return variable * (is_neg?-1:1);
}

int graph_negate(int vertex) {
    return sat_to_graph(-graph_to_sat(vertex));
}

void print_vector(std::vector<int>& vec) {
    for(auto v : vec) std::clog << v << " ";
    std::clog << std::endl;
}

void terminate_with_error(std::string error_msg) {
    std::cerr << "c \nc " << error_msg << std::endl;
    exit(1);
}

[[maybe_unused]] static void print_automorphism(int n, const int *p, int nsupp, const int *supp) {
    static dejavu::markset test_set;
    test_set.initialize(n);
    test_set.reset();
    for(int i = 0; i < nsupp; ++i) {
        const int v_from = supp[i];
        if(test_set.get(v_from)) continue;
        int v_next = p[v_from];
        if(v_from == v_next) continue;
        test_set.set(v_from);
        std::clog << "(" << v_from;
        while(!test_set.get(v_next)) {
            test_set.set(v_next);
            std::clog << " " << v_next;
            v_next = p[v_next];
        }
        std::clog << ")";
    }
    std::clog << std::endl;
}

static int hash32shift(int key) {
    key = ~key + (key << 15); // key = (key << 15) - key - 1;
    key = key ^ (key >> 12);
    key = key + (key << 2);
    key = key ^ (key >> 4);
    key = key * 2057; // key = (key + (key << 3)) + (key << 11);
    key = key ^ (key >> 16);
    return key;
}


// Hash function
struct any_hash
{
    long operator()(const std::vector<int>
                    &myVector) const
    {
        long answer = myVector.size();

        for (int i : myVector)
        {
            answer ^= hash32shift(i) + 0x9e3779b9 +
                      (answer << 6) + (answer >> 2);
        }
        return answer;
    }
};

struct triple_hash {
    inline std::size_t operator()(const std::tuple<int,int,int> & v) const {
        return 48*std::get<0>(v)+24*hash32shift(std::get<1>(v))+hash32shift(std::get<2>(v));
    }
};

struct pair_hash {
    std::size_t operator()(const std::pair<int,int> & v) const {
        return v.first*31+hash32shift(v.second);
    }
};
