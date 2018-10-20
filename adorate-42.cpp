#include <iostream>
#include <fstream>
#include <string>
#include <sstream>
#include <algorithm>
#include <vector>
#include <queue>
#include <unordered_set>
#include <unordered_map>
#include <thread>
#include <atomic>

#include "blimit.hpp"

using std::vector;
using std::unordered_set;
using std::priority_queue;
using std::unordered_map;
using std::string;

const int MAX_N_OF_THREADS = 103;

vector<unsigned int> rev_vertices_map;
unordered_map<unsigned int, unsigned int> vertices_map;

struct edge {
    int dest;
    int weight;

    edge(int d, int w) : dest(d), weight(w) {};
    edge() : dest(-1), weight(-1) {};
};

inline bool operator>(const edge e1, const edge e2) {
    if(e1.weight > e2.weight) {
        return true;
    }
    else if(e1.weight == e2.weight) {
        if(rev_vertices_map[e1.dest] > rev_vertices_map[e2.dest]) {
            return true;
        }
    }
    return false;
}

struct unique_integers_vector {
    vector<int> V;
    vector<bool> in_V;
    std::atomic_flag lock = ATOMIC_FLAG_INIT;

    unique_integers_vector() {
        lock.clear();
    }
    unique_integers_vector(const unique_integers_vector& other) {
        V = other.V;
        in_V = other.in_V;
        lock.clear();
    }
    unique_integers_vector(unique_integers_vector&& other) noexcept {
        V = std::move(other.V);
        in_V = std::move(other.in_V);
        lock.clear();
    }

    unique_integers_vector& operator=(const unique_integers_vector& other) {
        if (this != &other) {
            V = other.V;
            in_V = other.in_V;
        }

        return *this;
    }
    unique_integers_vector& operator=(unique_integers_vector&& other) noexcept {
        if (this != &other) {
            V = std::move(other.V);
            in_V = std::move(other.in_V);
        }

        return *this;
    }

    inline void no_sync_try_push_back(int elem) {
        if(!in_V[elem]) {
            V.push_back(elem);
            in_V[elem] = true;
        }
    }

    inline bool safe_try_set_flag(int elem) {
        if(!in_V[elem]) {
            in_V[elem] = true;
            return true;
        }
        return false;
    }

    void push_back_already_set(int elem) {
        while (lock.test_and_set()) {}
        V.push_back(elem);
        lock.clear();
    }

    void clear() {
        while (lock.test_and_set()) {}

        V.clear();
        std::fill(in_V.begin(), in_V.end(), false);

        lock.clear();
    }

    //we assume we use these functions only in non-parallel situations:
    inline vector<int>::const_iterator begin() {
        return V.begin();
    }

    inline vector<int>::const_iterator end() {
        return V.end();
    }
    inline bool empty() const {
        return V.empty();
    }
    inline unsigned long size() const {
        return V.size();
    }
    inline int operator[](unsigned int index) const {
        return V[index];
    }

    void resize_data(unsigned int max_index) {
        in_V.resize(max_index);
    }

    void initialize() {
        std::fill(in_V.begin(), in_V.end(), false);
    }
};

vector<vector<edge>> N;

vector<unordered_set<int>> T;
vector<int> b, db;
vector<int> next_db;

std::atomic_flag* vertex_lock;
std::atomic_flag* vertex_db_and_R_lock;

struct parallel_vector_of_limited_edge_PQs {
    vector<priority_queue<edge, vector<edge>, std::greater<>>> data;

    inline edge safe_last_edge(unsigned int v) {
        if(((int)data[v].size() < b[v]) || data[v].empty()) {
            return {-1, -1};
        }
        return data[v].top();
    }
    inline int safe_last(unsigned int v) {
        return safe_last_edge(v).dest;
    }
    edge last_edge(unsigned int v) {
        edge result;
        while(vertex_lock[v].test_and_set()) {}
        result = safe_last_edge(v);
        vertex_lock[v].clear();
        return result;
    }

    inline void safe_push(unsigned int index, edge e) {
        data[index].push(e);
        if((int)data[index].size() > b[index]) {
            data[index].pop();
        }
    }

    void no_sync_resize_data(unsigned int max_index) {
        data.resize(max_index);
    }

    inline bool no_sync_empty(unsigned int index) {
        return data[index].empty();
    }

    edge no_sync_top(unsigned int index) {
        return data[index].top();
    }
    void no_sync_pop(unsigned int index) {
        data[index].pop();
    }
};

parallel_vector_of_limited_edge_PQs S;

unique_integers_vector V, Q, R;

unsigned int max_index = 0;
static unordered_map<unsigned int, unsigned int>::const_iterator mapped_val_iter;

unsigned int get_mapped_index(unsigned int v) {
    mapped_val_iter = vertices_map.find(v);
    if(mapped_val_iter == vertices_map.end()) {
        rev_vertices_map.push_back(v);
        vertices_map[v] = max_index;
        N.emplace_back(vector<edge>());
        max_index++;
    }
    return vertices_map[v];
}

vector<int> last_arg_max;

edge arg_max(int v) {
    edge cur_edge;
    for(unsigned int i = (last_arg_max[v] + 1); i < N[v].size(); i++) {
        cur_edge = N[v][i];
        if(T[v].count(cur_edge.dest) == 0) {
            if(edge(v, cur_edge.weight) > S.last_edge(cur_edge.dest)){
                last_arg_max[v] = i;
                return cur_edge;
            }
        }
    }
    last_arg_max[v] = N[v].size();
    return {-1, -1};
}

void read_graph(const string& filename) {
    std::ifstream input_stream;
    std::string line;
    std::stringstream line_stream;
    unsigned int v_a, v_b;
    int w;

    try {
        input_stream.open(filename, std::ios::in);

        while(getline(input_stream, line)) {
            if(!line.empty()) {
                if(line[0] != '#') {
                    line_stream.str(line);
                    line_stream >> v_a >> v_b >> w;

                    line_stream.clear();

                    v_a = get_mapped_index(v_a);
                    v_b = get_mapped_index(v_b);

                    N[v_a].emplace_back(edge(v_b, w));
                    N[v_b].emplace_back(edge(v_a, w));
                }
            }
        }
    } catch (std::exception& e) {
        std::cerr << "Problem with reading a file" << std::endl;
    }
    input_stream.close();
}

void resize_structures(unsigned int max_index) {
    T.resize(max_index);
    S.no_sync_resize_data(max_index);

    b.resize(max_index);
    db.resize(max_index);
    next_db.resize(max_index);

    last_arg_max.resize(max_index);

    Q.resize_data(max_index);
    V.resize_data(max_index);
    R.resize_data(max_index);

    vertex_lock = new std::atomic_flag[max_index];
    vertex_db_and_R_lock = new std::atomic_flag[max_index];
}
void cleanup() {
    delete[] vertex_lock;
    delete[] vertex_db_and_R_lock;
}

const int main_thread_number = 0;

vector<std::thread> threads;
int thread_count = 1;

template<typename Fn, typename... Args>
void parallel_execute(Fn&& fn, Args&&... args) {
    for(int i = 1; i < thread_count; i++) {
        threads.emplace_back(std::thread(fn, i, args...));
    }

    fn(main_thread_number, args...);

    for (auto &thread : threads) {
        thread.join();
    }
    threads.clear();
}

void sort_selected_edges(unsigned int thread_number) {
    for(unsigned int i = thread_number; i < max_index; i += thread_count){
        sort(N[i].begin(), N[i].end(), std::greater<>());
    }
}
void initialize_selected_b(unsigned int thread_number, unsigned int b_method) {
    for(unsigned int i = thread_number; i < max_index; i += thread_count) {
        b[i] = bvalue(b_method, rev_vertices_map[i]);
    }
}

int partial_result[MAX_N_OF_THREADS];
void calculate_selected_results_and_clear_S_and_T(unsigned int thread_number) {
    partial_result[thread_number] = 0;
    for(unsigned int v = thread_number; v < max_index; v += thread_count) {
        while(!S.no_sync_empty(v)) {
            partial_result[thread_number] += S.no_sync_top(v).weight;
            S.no_sync_pop(v);
        }
        T[v].clear();
    }
}

void initialize_structures() {
    Q.initialize();
    V.initialize();
    R.initialize();

    std::fill(next_db.begin(), next_db.end(), 0);

    for(unsigned int i = 0; i < max_index; i++) {
        V.no_sync_try_push_back(i);
    }

    for(unsigned int i = 0; i < max_index; i++) {
        vertex_lock[i].clear();
        vertex_db_and_R_lock[i].clear();
    }
}
inline bool vertices_cmp(int v, int u) {
    if(N[v].empty()) {
        return false;
    }
    else { //N[v] is not empty
        if(N[u].empty()) {
            return true;
        }
        else { //N[v] is not empty and N[u] is not empty
            return ((N[v].begin()->weight) > (N[u].begin()->weight));
        }
    }
}
void sort_vertices() { //assumes edges are already sorted
    sort(V.V.begin(), V.V.end(), vertices_cmp);
}

void update_db() {
    for(auto i : R) {
        db[i] += next_db[i];
        next_db[i] = 0;
    }
}
int get_result_and_clear_S_and_T() {
    int result = 0;
    parallel_execute(calculate_selected_results_and_clear_S_and_T);
    for(int i = 0; i < thread_count; i++) {
        result += partial_result[i];
    }
    return result / 2;
}

void suit(unsigned int thread_number) {
    int x, y;
    edge x_edge;
    bool to_set = false;
    for(unsigned int i = thread_number; i < Q.size(); i += thread_count) {
        int u = Q[i];

        while((int)T[u].size() < (b[u] + db[u])) {
            x_edge = arg_max(u);
            x = x_edge.dest;

            if(x == (-1)) {
                break;
            }
            else {
                while (vertex_lock[x].test_and_set()) {}
                if (edge(u, x_edge.weight) > S.safe_last_edge(x)) { //still eligible
                    y = S.safe_last(x);

                    S.safe_push(x, edge(u, x_edge.weight));

                    vertex_lock[x].clear();

                    T[u].insert(x);

                    if (y != (-1)) {
                        //T[y].erase(x); - we would not ever take x to suit either, so instead of erasing it, we increment db[y]

                        while(vertex_db_and_R_lock[y].test_and_set()) {}

                        next_db[y]++;
                        to_set = R.safe_try_set_flag(y);

                        vertex_db_and_R_lock[y].clear();

                        if(to_set){
                            R.push_back_already_set(y);
                        }
                    }
                }
                else {
                    vertex_lock[x].clear();
                }
            }
        }
    }
}

int main(int argc, char* argv[]) {
    if (argc != 4) {
        std::cerr << "usage: "<<argv[0]<<" thread-count inputfile b-limit"<< std::endl;
        return 1;
    }

    thread_count = std::stoi(argv[1]);
    int b_limit = std::stoi(argv[3]);
    std::string input_filename{argv[2]};

    read_graph(input_filename);
    resize_structures(max_index);
    initialize_structures();
    parallel_execute(sort_selected_edges);
    sort_vertices();
    for (int b_method = 0; b_method < b_limit + 1; b_method++) {

        parallel_execute(initialize_selected_b, b_method);

        std::fill(db.begin(), db.end(), 0);
        std::fill(last_arg_max.begin(), last_arg_max.end(), -1);

        Q = V;
        while(!Q.empty()) {
            parallel_execute(suit);

            update_db();

            std::swap(Q, R);
            R.clear();
        }

        std::cout << get_result_and_clear_S_and_T() << std::endl;
    }
    cleanup();
}
