#include <cstdio>
#include <random>
#include <set>
#include <unordered_map>
#include <iostream>

using namespace std;


int main()
{
    random_device rd;
    mt19937_64 gen(rd());
    uniform_int_distribution<uint32_t> dis;

    unordered_map<string, string> od;
    while (od.size() < 1 * 1024 * 1024) {
        uint32_t n = dis(gen);
        if (n == 0) {
            continue;
        }

        uint32_t v = 0;
        while (!v) {
            v = dis(gen);
        }

        od.insert(make_pair(string((const char *)&n, 4), string((const char *)&v, 4)));
    }

    FILE * f = fopen("../data/000.dat", "wb");
    for (auto & d: od) {
        fwrite(d.first.c_str(), 4, 1, f);
        fwrite(d.second.c_str(), 4, 1, f);
    }
    fclose(f);

    return 0;
}
