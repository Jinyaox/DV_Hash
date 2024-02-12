#ifndef SHIFTINGHASHTABLE17_ALGO_EXP_H
#define SHIFTINGHASHTABLE17_ALGO_EXP_H

#include <cstdint>
#include <chrono>

typedef std::chrono::high_resolution_clock Clock;

struct KVPair {
    uint32_t key;
    uint32_t val;
};

class AlgoBase
{
public:
    virtual void set_data(KVPair * _data, int _num) = 0;
    virtual void run() = 0;
    virtual ~AlgoBase() = default;
};

template<class T>
class AlgoExp: public AlgoBase
{
    T * algo;
    KVPair * data;
    int num;
public:
    AlgoExp() {
        algo = new T();
    }

    void set_data(KVPair * _data, int _num)
    {
        data = _data;
        num = _num;
    }

    void run() {
        int suc_insert_num = 0;

        cout << "Build start" << endl;
        for (int i = 0; i < num; ++i) {
            bool result = algo->insert(data[i].key, data[i].val);
            if (!result) {
                suc_insert_num = i;
                cout << i << " failed" << endl;
                cout << double(i) / num << endl;
                break;
            }
            if ((i % (num / 10)) == 0) {
                cout << ".";
            }
        }
        cout << "done" << endl;

        // correctness check
        bool correct = true;
        for (int i = 0; i < suc_insert_num; ++i) {
            uint32_t ret = algo->query(data[i].key);
            if (ret != data[i].val) {
                cout << "query error" << endl;
                cout << i << " " << ret << endl;
                correct = false;
                break;
            }
        }

        if (correct) {
            cout << "start speed test" << endl;
            uint32_t accumulated = 0;

            auto t1 = Clock::now();

            constexpr int epoch = 1;

            for (int k = 0; k < epoch; k++) {
                for (int i = 0; i < suc_insert_num; ++i) {
                    uint32_t ret = algo->query(data[i].key);
                    accumulated += ret;
                }
            }

            auto t2 = Clock::now();

            int64_t nano = chrono::nanoseconds(t2 - t1).count();

            algo->report();
//        cout << nano << endl;
//            cout << "FP: " << double(ht->false_positive_probe) / (suc_insert_num * epoch) << endl;
            cout << epoch * suc_insert_num / double(nano) * 1000 << "MOPS" << endl;
            cout << accumulated << endl;
        }
    }

    ~AlgoExp()
    {
        delete algo;
    }
};

#endif //SHIFTINGHASHTABLE17_ALGO_EXP_H
