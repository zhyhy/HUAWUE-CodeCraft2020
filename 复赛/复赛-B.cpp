/**
 * @file 复赛-B.cpp
 * @brief 使用静态数组建图+visited3_2_1+迭代的predfs
 * @author ZHY
 * @version 7.0
 * @date 2020-05-15
 */
#include <algorithm>
#include <chrono>
#include <iostream>
#include <assert.h>
#include <string>
#include <unordered_map>
#include <vector>
#include <thread>
#include <mutex>
#include <sys/mman.h>
#include <sys/types.h>
#include <sys/stat.h>
#include <fcntl.h>
#include <unistd.h>
#include <string.h>
#include <math.h>
#include <random>

#define MAX_EDGE_NUM 2000000            // 数据集中给定的大小
#define MAX_VERTEX_NUM 520000           // 自己猜测设定的大小
#define THREADNUM 4
#define FAST1 1     //00000001
#define FAST2 2     //00000010
#define FAST32 6    //00000110

// #define DEBUG
// #define DEBUG1

using namespace std;
typedef unsigned int u32_t;
typedef unsigned long long u64_t;

// 定义宏
#define N_5(n) (((u64_t)n << 2 ) + n)
#define N_3(n) (((u64_t)n << 1 ) + n)
#define MIN(a,b) ((a) < (b) ? (a) : (b))
#define MAX(a,b) ((a) > (b) ? (a) : (b))

struct Node {
    u32_t to;
    u64_t amount;
    Node() {
        to = 0;
        amount = 0;
    }
    // 升序排序函数
    bool operator<(const Node& node) const { return to < node.to; }
};

struct AccoutComma {
    char accoutComma[12];  // 存储'account'+','
    u32_t len;             // 存储account+','的长度
    AccoutComma() { len = 0; }
};

// 工具函数
inline int u32_tToChar(char *destStr, u32_t val, bool comma_or_enter);
inline u32_t charTou32_t(char *string, u32_t& len);
inline u64_t amoutTou64_t(char* string, u32_t& len);
inline int binarySearch(Node* a, const u32_t start, const u32_t end, const u32_t key);
inline u32_t mylower_bound(Node* startA, const u32_t start, const u32_t end, const u32_t tar);
inline u32_t mylower_bound(u32_t* startA, const u32_t start, const u32_t end, const u32_t tar);
inline bool checkFirstMoney(u64_t max, u64_t min, u64_t amout);
inline bool checkMoney(u64_t pre, u64_t cur);

class TicToc {
  public:
    TicToc() {
        tic();
    }

    void tic() {
        start = std::chrono::system_clock::now();
    }

    double toc() {
        end = std::chrono::system_clock::now();
        std::chrono::duration<double> elapsed_seconds = end - start;  
        start = std::chrono::system_clock::now();
        return elapsed_seconds.count();
    }

  private:
   chrono::time_point<std::chrono::system_clock> start, end;
};

class DirectedGraph {
   private:
    // 建图相关变量  
	u32_t nodeCnt_;
    static Node Graph_[MAX_EDGE_NUM];
    static u32_t invGraph_[MAX_EDGE_NUM];
    static u32_t Graph_start_end_[MAX_VERTEX_NUM][2];
    static u32_t invGraph_start_end_[MAX_VERTEX_NUM][2];
    static AccoutComma accoutComma_[MAX_VERTEX_NUM];

    // 环的路径结果
    vector<vector<u32_t>> ans_[THREADNUM][9];     // 四个线程，每一个线程的结果存储在vector<Path> [8]中
    static u32_t ansCnt_[THREADNUM] ;      
    static char ansBuf_[2000*1024*1024];

    string inputFile_;
    string outputFile_;

   public:
    DirectedGraph(const string &inputFile, const string &outputFile)
        : inputFile_(inputFile), outputFile_(outputFile) {
    }
  
    /**
     * @brief 读取文件，建立正向以及逆向邻接表
     *
     * @return 
     */
    bool parseInputFileAndMap() {
        struct stat sb;
        int fd = open(inputFile_.c_str(), O_RDONLY);
        if (fd < 0) {
            cerr << "没有读取到文件！！" << endl;
            exit(0);
        }
        fstat(fd, &sb);
        char *start = (char *)mmap(NULL, sb.st_size, PROT_READ, MAP_SHARED, fd, 0);

        // 建立映射
        // key是account,val是<出度，入度>
        unordered_map<u32_t, pair<u32_t, u32_t>> outInDegrees;
		vector<u32_t> us, vs;
		vector<u64_t> amounts;
        amounts.reserve(2000000), us.reserve(2000000), vs.reserve(2000000);
        char *head = start;
        u32_t i = 0, u = 0, v = 0,next = 0;
        u64_t amount1,amount2;
        u64_t  amount;
        while (i < sb.st_size) {
            u = charTou32_t(head, next); // 123,125.25
            ++outInDegrees[u].first;  // first表示出度
            us.push_back(u);
            head += next;
            i += next;
            v = charTou32_t(head, next);
            ++outInDegrees[v].second; // second表示入度
            vs.push_back(v);
            head += next;
            i += next;
            amount1 = charTou32_t(head, next);
            head += next - 1;
            i += next - 1;
            // cout<<"u-->v "<<u<<"--"<<v<<"是否是逗号："<<*head<<endl;
            if (*head == '.') {
                head += 1;
                i += 1;
                amount2 = charTou32_t(head, next);
                // cout<<"NEXT的长度："<<next<<endl;
                if (next == 3) {  // /r/n
                    amount2 *=10;
                }
                head += next;
                i += next;
                amount = u64_t(100)*amount1+amount2;
            } else {
                head += 1;
                i+=1;
                amount = u64_t(100) * amount1;
            }
            amounts.push_back(amount);
            // head += next;
            // i += next;
            // cout<<" u-->v : 100*amount "<u<<" -- "<<v<<" : "<<amount<<endl;
        }
        nodeCnt_ = outInDegrees.size();
        vector<u32_t> idToAccount;
        idToAccount.reserve(nodeCnt_);
        for (auto &x : outInDegrees) {
            idToAccount.push_back(x.first);
        }
        sort(idToAccount.begin(), idToAccount.end());
        unordered_map<u32_t, u32_t> accountToId;
        accountToId.reserve(nodeCnt_);
        Node* pgraph[nodeCnt_] = {NULL};
        u32_t* pinvgraph[nodeCnt_] = {NULL};
        u32_t totalOutDegree = 0, totalInDegree = 0;
        u32_t accout;
        for (u32_t node = 0; node < nodeCnt_; ++node) {
            accout = idToAccount[node];
            accountToId[accout] = node;
            Graph_start_end_[node][0] = totalOutDegree;
            pgraph[node] = Graph_+ totalOutDegree;
            totalOutDegree += outInDegrees[accout].first;
            Graph_start_end_[node][1] = totalOutDegree;

            invGraph_start_end_[node][0] = totalInDegree;
            pinvgraph[node] = invGraph_ + totalInDegree;
            totalInDegree += outInDegrees[accout].second;
            invGraph_start_end_[node][1] = totalInDegree;
        }

        // 建立邻接表
        u32_t idu,idv;
        for (u32_t j = 0; j < us.size(); ++j) {
            u = us[j];
            v = vs[j];
            amount = amounts[j];
            if(amount == 0) continue;
            idu = accountToId[u];
            idv = accountToId[v];
            pgraph[idu]->to = idv;
            pgraph[idu]->amount = amount;
            ++pgraph[idu];
            *pinvgraph[idv]++ = idu;
            if (!accoutComma_[idu].len) {
                accoutComma_[idu].len = u32_tToChar(accoutComma_[idu].accoutComma, u, true);
            }
            if (!accoutComma_[idv].len) {
                accoutComma_[idv].len = u32_tToChar(accoutComma_[idv].accoutComma, v, true);
            }
        }
        close(fd);
        munmap(start, sb.st_size);
#ifdef DEBUG
        cout << "一共读取到 " << nodeCnt_ << "个节点" << endl;
        cout<<"图的总出度为："<<totalOutDegree<<" 总入度为："<<totalInDegree<<endl;
#endif
#ifdef DEBUG1
        random_device dev;
        mt19937 rng(dev());
        std::uniform_int_distribution<mt19937::result_type> dist(0, nodeCnt_);
        u32_t _u, _v, _amount;
        _u = dist(rng);
        cout<<idToAccount[_u]<<"的出度为："<<outInDegrees[idToAccount[_u]].first<<endl;
        for (u32_t i = Graph_start_end_[_u][0]; i < Graph_start_end_[_u][1]; ++i) {
            _v = Graph_[i].to;
            _amount = Graph_[i].amount;
            cout << "u-->v : amount " << idToAccount[_u] << "-->" << idToAccount[_v] << " : " << _amount << endl;
        }
#endif
        return true;
    }

    /**
     * @brief 出度和入度都升序排列
     */
    bool graphSort() {
        for (u32_t i = 0; i < nodeCnt_; ++i) {
            sort(Graph_ + Graph_start_end_[i][0], Graph_ + Graph_start_end_[i][1]);
            sort(invGraph_ + invGraph_start_end_[i][0], invGraph_ + invGraph_start_end_[i][1]);
        }
        return true;
    }

    /**
     * @brief 拼接结果中的字符串
     *
     * @param start 存储字符串的首地址
     * @param offset 返回字符串长度
     * @param layer 层数3~7
     */
    void constructString(char* start, size_t& offset, const int layer) {
        vector<vector<u32_t>>::iterator path_iter[THREADNUM];
        vector<vector<u32_t>>::iterator path_iter_end[THREADNUM];
        vector<vector<u32_t>>::iterator tmp_path;
        register u32_t u,len;
        register char* tempPointer;
        for (u32_t i = 0; i < THREADNUM; ++i) {
            path_iter[i] = ans_[i][layer].begin();
            path_iter_end[i] = ans_[i][layer].end();
        }
        for (u32_t i = 0; i < nodeCnt_; ++i) {
            u32_t path_idx = i % THREADNUM;
            if (path_iter[path_idx] == path_iter_end[path_idx]) continue;
            tmp_path = path_iter[path_idx];
            while ((*tmp_path)[0] == i) {
                for (u32_t j = 0; j < tmp_path->size(); ++j) {
                    u = (*tmp_path)[j];
                    tempPointer = accoutComma_[u].accoutComma;
                    len = accoutComma_[u].len;
                    memcpy(start + offset, tempPointer, len);
                    offset += len;
                }
                *(start + offset - 1) = '\n';
                if (++path_iter[path_idx] == path_iter_end[path_idx]) break;
                tmp_path = path_iter[path_idx];
            }
        }
    }

    void save_result() {
        TicToc time;
        remove(outputFile_.c_str());
        size_t off = 0;
        u32_t loop = 0;
        for(int i = 0; i < THREADNUM; ++i) {
            loop += ansCnt_[i];
        }
        off += u32_tToChar(ansBuf_, loop, false);
        for (int i = 3; i <= 8; ++i) {
            constructString(ansBuf_, off, i);
        }
#ifdef DEBUG
        cout << "一共找到了：" << loop << " 个环" << endl;
        cout<<"一共 "<<off<<" 字节长度的字符 "<<off/1024/1024<<" 兆"<<endl;
        cout<<"拼接字符串用时："<<time.toc()<<" s"<<endl;
#endif
        int fd  = open(outputFile_.c_str(), O_CREAT | O_RDWR | O_TRUNC, 0666);
        write(fd,ansBuf_,off);
        close(fd);
    }

    /**
     * @brief 多线程DFS的入口函数
     *
     * @param threadNo 线程的编号，例如8个线程，则是0~7
     */
    void dfsForMultithread(u32_t threadNo) {     
        TicToc time;
        bool visited[nodeCnt_] = {0};
        char visited3_2_1[nodeCnt_] = {0};
        u32_t path[8] = {0};

        u32_t* pathTail = path;
        u32_t* pathHead = path;
        u32_t init_max_min_amount[3] = {0};
        for (u32_t i = 0; i < nodeCnt_; ++i) {
            if (i % THREADNUM != threadNo) {
                continue;
            }
            memset(visited3_2_1,0,nodeCnt_*sizeof(char));
            preDfs(i,visited3_2_1,init_max_min_amount);
            dfs(i, i, 1, pathTail, pathHead, visited, visited3_2_1, threadNo, 1, init_max_min_amount);
        }
#ifdef DEBUG
        cout << "第 " << threadNo + 1 << "个线程DFS耗时：" << time.toc() * 1000 << " ms" << endl;
#endif 
    }

    /**
     * @brief 迭代的反向DFS
     *
     * @param head 开始点
     * @param visited3_2_1 {第三层邻居,第二层邻居，第一层层邻居}（按位标记）
     */
    void preDfs(u32_t head, char* visited3_2_1, u32_t* init_max_min_amount) {
        u32_t r_end = invGraph_start_end_[head][1];
        u32_t l1 = mylower_bound(invGraph_, invGraph_start_end_[head][0], r_end, head);
        for (; l1 < r_end; ++l1) {
            u32_t u1 = invGraph_[l1];
            if (u1 != head) {                 // 避免反向自环
                visited3_2_1[u1] |= 0x1;      // 第一层的标记，在第一位
                int idx1 = binarySearch(Graph_, Graph_start_end_[u1][0], Graph_start_end_[u1][1], head);
                u32_t cur_amount1 = Graph_[idx1].amount;
                init_max_min_amount[1] = MAX(init_max_min_amount[1], cur_amount1);
                init_max_min_amount[2] = MIN(init_max_min_amount[2], cur_amount1);
                u32_t r_end1 = invGraph_start_end_[u1][1];
                u32_t l2 = mylower_bound(invGraph_, invGraph_start_end_[u1][0], r_end1, head);
                for (l2; l2 < r_end1; ++l2) {
                    u32_t u2 = invGraph_[l2];  // 反向第2层 u2
                    int idx2 = binarySearch(Graph_, Graph_start_end_[u2][0], Graph_start_end_[u2][1], u1);
                    u32_t cur_amount2 = Graph_[idx2].amount;
                    if (u2 != head && u2 != u1 && checkMoney(cur_amount2, cur_amount1)) {
                        visited3_2_1[u2] |= 2;  // 第二层的标记，在第二位
                        u32_t r_end2 = invGraph_start_end_[u2][1];
                        u32_t l3 = mylower_bound(invGraph_, invGraph_start_end_[u2][0], r_end2, head);
                        for (l3; l3 < r_end2; ++l3) {
                            u32_t u3 = invGraph_[l3];  // 反向第3层 u3
                            int idx3 = binarySearch(Graph_, Graph_start_end_[u3][0], Graph_start_end_[u3][1], u2);
                            u32_t cur_amount3 = Graph_[idx3].amount;
                            if (u3 != head && u3 != u2 && checkMoney(cur_amount3, cur_amount2)) {
                                visited3_2_1[u3] |= 4;
                            }
                        }
                    }
                }
            }
        }
        return;
    }

    void dfs(u32_t head, u32_t cur, u32_t depth, u32_t* pathTail, u32_t* pathHead, bool* visited, char* visited3_2_1, u32_t threadNo, u32_t pre_amount,u32_t* init_max_min_amount) {
        cout<<"进入前向DFS"<<endl;
        visited[cur] = true;
        *pathTail++ = cur;
        u32_t l_start = Graph_start_end_[cur][0];
        u32_t r_end = Graph_start_end_[cur][1];
        u32_t i = mylower_bound(Graph_,l_start,r_end, head);
        for (; i < r_end; ++i) {
            u32_t v = Graph_[i].to;
            u32_t cur_amount = Graph_[i].amount;
            switch (depth) {
                case (1): {
                    init_max_min_amount[0] = cur_amount;
                    if (!visited[v]) {
                        // 使用反向的金额范围约束，决定是否进入下一层
                        if(checkFirstMoney(init_max_min_amount[1], init_max_min_amount[2], cur_amount)) {
                        dfs(head, v, depth + 1, pathTail, pathHead, visited, visited3_2_1, threadNo, cur_amount, init_max_min_amount);
                        }
                        break;
                    }
                }
                case (2): {
                    if (visited3_2_1[v] & FAST1 && !visited[v] && checkMoney(pre_amount, cur_amount)) {
                        int idx = binarySearch(Graph_,Graph_start_end_[v][0],Graph_start_end_[v][1], head);
                        u32_t amoutX = Graph_[idx].amount;
                        if (checkMoney(cur_amount, amoutX) && checkMoney(amoutX, init_max_min_amount[0])) {
                            ++ansCnt_[threadNo];
                            *pathTail++ = v;
                            ans_[threadNo][depth + 1].emplace_back(vector<u32_t>(pathHead, pathTail));
                            *(--pathTail) = 0;
                        }
                    }
                    if (checkMoney(pre_amount, cur_amount) && !visited[v]) {
                        dfs(head, v, depth + 1, pathTail, pathHead, visited, visited3_2_1, threadNo, cur_amount, init_max_min_amount);
                    }
                    break;
                }
                case (3): {
                    if (visited3_2_1[v] & FAST1 && !visited[v] && checkMoney(pre_amount, cur_amount)) {
                        int idx = binarySearch(Graph_, Graph_start_end_[v][0],Graph_start_end_[v][1], head);
                        u32_t amoutX = Graph_[idx].amount;
                        if (checkMoney(cur_amount, amoutX) && checkMoney(amoutX, init_max_min_amount[0])) {
                            ++ansCnt_[threadNo];
                            *pathTail++ = v;
                            ans_[threadNo][depth + 1].emplace_back(vector<u32_t>(pathHead, pathTail));
                            *(--pathTail) = 0;
                        }
                    }
                    if (checkMoney(pre_amount, cur_amount) && !visited[v]) {
                        dfs(head, v, depth + 1, pathTail, pathHead, visited, visited3_2_1, threadNo, cur_amount, init_max_min_amount);
                    }
                    break;
                }
                case (4): {
                    if (visited3_2_1[v] & FAST1 && !visited[v] && checkMoney(pre_amount, cur_amount)) {
                        int idx = binarySearch(Graph_, Graph_start_end_[v][0], Graph_start_end_[v][1], head);
                        u32_t amoutX = Graph_[idx].amount;
                        if (checkMoney(cur_amount, amoutX) && checkMoney(amoutX, init_max_min_amount[0])) {
                            ++ansCnt_[threadNo];
                            *pathTail++ = v;
                            ans_[threadNo][depth + 1].emplace_back(vector<u32_t>(pathHead, pathTail));
                            *(--pathTail) = 0;
                        }
                    }
                    if(visited3_2_1[v] & FAST32 && !visited[v] && checkMoney(pre_amount,cur_amount)){
                        dfs(head, v, depth + 1, pathTail, pathHead, visited, visited3_2_1, threadNo, cur_amount, init_max_min_amount);
                    }
                    break;
                }
                case (5): {
                    if (visited3_2_1[v] & FAST1 && !visited[v] && checkMoney(pre_amount, cur_amount)) {
                        int idx = binarySearch(Graph_ ,Graph_start_end_[v][0],Graph_start_end_[v][1], head);
                        u32_t amoutX = Graph_[idx].amount;
                        if (checkMoney(cur_amount, amoutX) && checkMoney(amoutX, init_max_min_amount[0])) {
                            ++ansCnt_[threadNo];
                            *pathTail++ = v;
                            ans_[threadNo][depth + 1].emplace_back(vector<u32_t>(pathHead, pathTail));
                            *(--pathTail) = 0;
                        }
                    }
                    if (visited3_2_1[v] & FAST2 && !visited[v] && checkMoney(pre_amount, cur_amount)) {
                        dfs(head, v, depth + 1, pathTail, pathHead, visited, visited3_2_1, threadNo, cur_amount, init_max_min_amount);
                    }
                    break;
                }
                case (6): {
                    if (visited3_2_1[v] & FAST1 && !visited[v] && checkMoney(pre_amount, cur_amount)) {
                        int idx = binarySearch(Graph_,Graph_start_end_[v][0],Graph_start_end_[v][1], head);
                        u32_t amoutX = Graph_[idx].amount;
                        if (checkMoney(cur_amount, amoutX) && checkMoney(amoutX, init_max_min_amount[0])) {
                            ++ansCnt_[threadNo];
                            *pathTail++ = v;
                            ans_[threadNo][depth + 1].emplace_back(vector<u32_t>(pathHead, pathTail));
                            *(--pathTail) = 0;
                        }
                    }
                    break;
                }
            }
        }
        visited[cur] = false;
        *(--pathTail) = 0;
        return;
    }

    void preDfs(u32_t head, u32_t cur, u32_t depth, bool* visited, char* visited3_2_1, u32_t pre_amount, u32_t* init_max_min_amount) {
        register u32_t temp_l, temp_r;
        u32_t l_start = invGraph_start_end_[cur][0];
        u32_t r_end = invGraph_start_end_[cur][1];
        u32_t i = mylower_bound(invGraph_, l_start, r_end, head);
        for (; i < r_end; ++i) {
            u32_t u = invGraph_[i];
            if (visited[u]) continue;
            temp_l = Graph_start_end_[u][0];
            temp_r = Graph_start_end_[u][1];
            int idx = binarySearch(Graph_, temp_l, temp_r, cur);
            u32_t cur_amount = Graph_[idx].amount;

            switch (depth) {
                case (2): {
                    visited3_2_1[u] |= 0x2;
                    visited[u] = true;
                    preDfs(head, u, depth + 1, visited, visited3_2_1, cur_amount, init_max_min_amount);
                    visited[u] = false;
                    break;
                }
                case (1): {
                    visited3_2_1[u] |= 0x1;
                    visited[u] = true;
                    preDfs(head, u, depth + 1, visited, visited3_2_1, cur_amount, init_max_min_amount);
                    visited[u] = false;
                    break;
                }
                case (3): {
                    // visited[u] = true;
                    visited3_2_1[u] |= 0x4;
                    break;
                }
            }

        }
        return;
    }
};

Node DirectedGraph::Graph_[MAX_EDGE_NUM];
u32_t DirectedGraph::invGraph_[MAX_EDGE_NUM];
u32_t DirectedGraph::Graph_start_end_[MAX_VERTEX_NUM][2];
u32_t DirectedGraph::invGraph_start_end_[MAX_VERTEX_NUM][2];
AccoutComma DirectedGraph::accoutComma_[MAX_VERTEX_NUM];
u32_t DirectedGraph::ansCnt_[THREADNUM] = {0};
char DirectedGraph::ansBuf_[2000 * 1024 * 1024];

int main(int argc, char **argv){
    TicToc totalTime;
    unordered_map<string,string> inputFiles;

    inputFiles["43"]       = "../Dataset/43/test_data.txt";
    inputFiles["54"]       = "../Dataset/54/test_data.txt";
    inputFiles["321"]       = "../Dataset/321/test_data.txt";
    inputFiles["5.16"]       = "../Dataset/5.16/test_data.txt";
    inputFiles["26571"]       = "../Dataset/26571/test_data.txt";
    inputFiles["1004812"]  = "../Dataset/1004812/test_data.txt";
    inputFiles["697518"]   = "../Dataset/697518/test_data.txt";
    inputFiles["1305172"]  = "../Dataset/1305172/test_data.txt";
    inputFiles["19630345"] = "../Dataset/19630345/test_data.txt";
    inputFiles["38556797"] = "../Dataset/38556797/test_data.txt";
    inputFiles["1004812"] = "../Dataset/1004812/test_data.txt";

    string outputFile = "./vectorResult.txt";

    // string inputFile = "/data/test_data.txt";
    // string outputFile = "/projects/student/result.txt";

    DirectedGraph solveGraph(inputFiles[argv[1]], outputFile);

    TicToc time;
    solveGraph.parseInputFileAndMap();
    cout << "读取文件+建图耗时：" << time.toc() << " s" << endl;

    solveGraph.graphSort();
    cout << "出边+入边排序耗时：" << time.toc() << " s" << endl;

    vector<thread> dfsObjs;
    for (int i = 0; i < THREADNUM; ++i) {
        dfsObjs.push_back(thread(&DirectedGraph::dfsForMultithread, &solveGraph, i));
    }
    for (auto it = dfsObjs.begin(); it < dfsObjs.end(); ++it) {
        it->join();
    }
    cout << THREADNUM << " 线程DFS耗时：" << time.toc() << " s" << endl;

    solveGraph.save_result();
    cout << "保存结果用时：" << time.toc() << " s" << endl;

    cout<<"程序用时："<<totalTime.toc()<<" s"<<endl;

    exit(0);

    return 0;
}


/**
 * @brief 整形数转换为char[]
 *
 * @param destStr char[]的数组，大小足够容纳转换后的值
 * @param val 要转换的int
 * @param comma_or_enter 为true，在末尾添加','，为false在末尾添加'\n'
 *
 * @return 字符串的长度
 */
inline int u32_tToChar(char *destStr, u32_t val, bool comma_or_enter) {
    static char index[]  = "0123456789";
    static char comma    = ',';
    static char lineFeed = '\n';
    static char endNull  = '\0';
    int i = 0, len = 0;
    char *head, *end, tmp;
    do {
        destStr[i++] = index[val % 10];
        val /= 10;
        len++;
    } while (val);

    head = destStr;            // 指向头部的指针
    end  = destStr + len - 1;  // 指向尾部的指针
    while (head < end) {       // 两极翻转；int 类型的1234在b中存储的是"4321"
        tmp     = *head;
        *head++ = *end;
        *end--  = tmp;
    }
    if (comma_or_enter) {
        destStr[len] = comma;
    } else {
        destStr[len] = lineFeed;
    }
    destStr[++len] = endNull;
    return len;
}

/**
 * @brief char[]转换为整形
 *
 * @param string 输入的char*指针
 * @param len 字符串长度+1
 *
 * @return 转换后的int
 */
inline u32_t charTou32_t(char *string, u32_t& len) {
    register u32_t value = 0;
    len = 1;
    while (*string >= '0' && *string <= '9') {
        value *= 10;
        value += *string - '0';
        ++string;
        ++len;
    }
    if (*string != ',' && *string !='.' && *string != '\r' && *string != '\n') value = 0;
    if (*string == '\r') ++len;
    return value;
}

inline u64_t amoutTou64_t(char* string, u32_t& len) {
    register u64_t value_zhengshu = 0;
    register u64_t value_xiaoshu = 0;
    u64_t plus = 100;
    while (*string >= '0' && *string <= '9') {
        value_zhengshu *= 10;
        value_zhengshu += *string - '0';
        ++string;
        ++len;
    }
    if (*string == '.') {
        ++string;
        ++len;
        while (*string >= '0' && *string <= '9') {
            value_xiaoshu *= 10;
            value_xiaoshu += *string - '0';
            ++string;
            ++len;
        }
    };
    u64_t amoutPlus = u64_t(100) * value_zhengshu + value_xiaoshu;
    if (*string != ',' && *string != '\r' && *string != '\n') {
        amoutPlus = 0;
    }
    if (*string == '\r') ++len;
    return amoutPlus;
}

inline int binarySearch(Node* a, const u32_t start, const u32_t end, const u32_t key) {
    u32_t low = start;
    u32_t high = end-1;
    while(low<= high){
        int mid = (low + high)/2;
        int midVal = a[mid].to;
        if(midVal < key)
            low = mid + 1;
        else if(midVal>key)
            high = mid - 1;
        else
            return mid;
    }
    return 0;
}
inline u32_t mylower_bound(Node* startA, const u32_t start, const u32_t end, const u32_t tar) {
    u32_t l = start;
    u32_t r = end;
    while (l < r) {
        u32_t mid = (l + r) >> 1;
        if (startA[mid].to >= tar) {
            r = mid;
        } else {
            l = mid + 1;
        }
    }
    return l;
}
inline u32_t mylower_bound(u32_t* startA, const u32_t start, const u32_t end, const u32_t tar) {
    u32_t l = start;
    u32_t r = end;
    while (l < r) {
        u32_t mid = (l + r) >> 1;
        if (startA[mid] >= tar) {
            r = mid;
        } else {
            l = mid + 1;
        }
    }
    return l;
}

inline bool checkMoney(u64_t pre, u64_t cur) {
    return pre <= N_5(cur) &&  cur <= N_3(pre);
}
inline bool checkFirstMoney(u64_t max_value, u64_t min_value, u64_t curY) {
    return min_value <= N_5(curY) && curY <= N_3(max_value);
}
