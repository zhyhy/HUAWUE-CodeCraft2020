/**
 * @file 多线程Baseline.cpp
 * @brief 出入度减枝+强连通分量减枝+反向DFS+正向DFS+减少1层DFS+多线程
 * @author ZHY
 * @version 1.2
 * @date 2020-04-19
 */
#include <algorithm>
#include <chrono>
#include <iostream>
#include <queue>
#include <string>
#include <unordered_map>
#include <vector>
#include <thread>
#include <atomic>
#include <mutex>
#include <sys/mman.h>
#include <sys/types.h>
#include <sys/stat.h>
#include <fcntl.h>
#include <unistd.h>
#include <string.h>

#define MAX_DEPTH 7
#define MIN_DEPTH 3
#define THREADNUM 4
#define DEBUG
// #define DEBUG1

using namespace std;

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

/**
 * @brief ID最小的第一个输出
 *        总体按照路径升序排列
 *        同一级别的路径长度下按照字典序（ID转为无符号整数后）升序排序
 */
struct Path {
    int length;
    vector<int> path;
    Path(int length, const vector<int> &path) : length(length), path(path) {}

};

class DirectedGraph {
   private:
    vector<vector<int>> Graph_;       
    vector<vector<int>> invGraph_;    
    unordered_map<int, int> idHash_;  
    vector<string> accoutComma_;      
    vector<string> accoutEnter_;
    vector<int> inputs_;
    vector<int> inDegrees_;           
    vector<int> outDegrees_;          
    vector<Path> ans_[THREADNUM][8];   // 四个线程，每一个线程的结果存储在vector<Path> [8]中
    int nodeCnt_;                     

	atomic<int> ansCnt_;               // 测试发现，原子操作并不过多影响多线程性能
	//int ansCnt_;

    string inputFile_;
    string outputFile_;

    // 求解强连通分量相关变量
    vector<int> scc_;                           
    unordered_map<int,vector<int>> sccIds_;               
    vector<int> low_;
    vector<int> dfn_;
    vector<int> stack_;
    int sccnum_;     

   public:
    DirectedGraph(const string& inputFile, const string& outputFile):inputFile_(inputFile),outputFile_(outputFile) {
        ansCnt_.store(0);
        inputs_.reserve(600000);
    }

    /**
     * @brief 读取.txt文件
     */
    bool parseInputFile() {
        FILE *pfile = fopen(inputFile_.c_str(), "r");
        if (pfile == NULL) {
            cout << "读取文件失败！" << endl;
            return false;
        }
        int u, v, c;
        int cnt = 0;
        while (fscanf(pfile, "%d,%d,%d", &u, &v, &c) != EOF) {
            inputs_.push_back(u);
            inputs_.push_back(v);
            ++cnt;
        }
#ifdef DEBUG
        cout << "一共读取到： " << cnt << " 条转帐记录。" << endl;
#endif
        return true;
    }

    /**
     * @brief 拼接第layer层的结果的字符串
     *
     * @param pathStr 拼接后的字符串
     * @param layer 要拼接的层数（3-7）
     */
	void constructString(string& pathStr, int layer) {
		pathStr.reserve(38000000);

		// 若要拼接第三层的路径
		// 这个迭代器指向每个线程计算得到的第三层路径
		vector<Path>::iterator path_iter[THREADNUM];
		for (int i = 0; i < THREADNUM; ++i) {
			path_iter[i] = ans_[i][layer].begin();
		}

		for (int i = 0; i < nodeCnt_; ++i) {
			int path_idx = i % THREADNUM;

			if (path_iter[path_idx] == ans_[path_idx][layer].end())
				continue;
			vector<int>& tmp_path = path_iter[path_idx]->path;
			while ((tmp_path[0] == i)) {
				for (int j = 0; j < tmp_path.size() - 1; ++j) {
					pathStr += accoutComma_[tmp_path[j]];
				}
				pathStr += accoutEnter_[tmp_path[tmp_path.size() - 1]];
				if (++path_iter[path_idx] == ans_[path_idx][layer].end())
					break;
				tmp_path = path_iter[path_idx]->path;
			}
		}
#ifdef DEBUG
        cout<<"第 "<<layer<<" 层的字符数量是："<<pathStr.length()<<endl;
#endif
	}

    /**
     * @brief 保存结果
     */
	void save_result_mmap() {
		TicToc time;
		string resStr[8];  

		char buf[1024];
        int idx = sprintf(buf, "%d\n", ansCnt_.load());
        buf[idx] = '\0';
		string ansCnt(buf);
		
		size_t sum_char = 0;
		sum_char += ansCnt.length();
		for (int i = MIN_DEPTH; i <= MAX_DEPTH; ++i) {
			constructString(resStr[i], i);
			sum_char += resStr[i].length();
		}
#ifdef DEBUG
		cout << "输出结果时拼接长度为：" << sum_char << " 的字符串用时：" << time.toc() << endl;
		cout << "一共找到了：" << ansCnt_.load() << " 个环" << endl;
#endif
		int fd = open(outputFile_.c_str(), O_CREAT | O_RDWR | O_TRUNC, 00777);
        truncate(outputFile_.c_str(), sum_char);
		char* pmap = (char*)mmap(NULL, sum_char, PROT_READ | PROT_WRITE, MAP_SHARED, fd, 0);
		char* head = pmap;
		memcpy(pmap, ansCnt.c_str(), ansCnt.length());
		pmap += ansCnt.length();
		for (int i = MIN_DEPTH; i <= MAX_DEPTH; ++i) {
			memcpy(pmap, resStr[i].c_str(), resStr[i].length());
			pmap += resStr[i].length();
		}
        msync(pmap, sum_char, MS_SYNC);
        munmap(pmap, sum_char);
        close(fd);
	}

    /**
     * @brief 映射 & 建图
     */
    bool constructGraph() {
        auto tmp = inputs_;

        sort(tmp.begin(), tmp.end());
        tmp.erase(unique(tmp.begin(), tmp.end()), tmp.end());
        nodeCnt_ = tmp.size();
        accoutComma_.reserve(nodeCnt_);
        accoutEnter_.reserve(nodeCnt_);
        int idx = 0;
        for (int &x : tmp) {
            accoutComma_.push_back(to_string(x) + ',');
            accoutEnter_.push_back(to_string(x) + '\n');
            idHash_[x] = idx++;
        }
        Graph_ = vector<vector<int>>(nodeCnt_);
        invGraph_ = vector<vector<int>>(nodeCnt_);
        inDegrees_ = vector<int>(nodeCnt_, 0);
        outDegrees_ = vector<int>(nodeCnt_, 0);
        int sz = inputs_.size();
        for (int i = 0; i < sz; i += 2) {
            int u = idHash_[inputs_[i]], v = idHash_[inputs_[i + 1]];
            Graph_[u].push_back(v);
            invGraph_[v].push_back(u);
            ++inDegrees_[v];
            ++outDegrees_[u];
        }
#ifdef DEBUG
        cout << "一共有： " << nodeCnt_ << "账户。" << endl;
#endif

        return true;
    }

    /**
     * @brief 使用topo排序实现对出度和入读进行减枝
     */
    bool branchReduction() {
        queue<int> inDegreesQueue;
        queue<int> outDegreesQueue;
        for (int i = 0; i < nodeCnt_; ++i) {
            if (inDegrees_[i] == 0) {
                inDegreesQueue.push(i);
            }
            if (outDegrees_[i] == 0) {
                outDegreesQueue.push(i);
            }
        }

        while (!inDegreesQueue.empty()) {
            int u = inDegreesQueue.front();
            inDegreesQueue.pop();
            for (int &v : Graph_[u]) {
                if (--inDegrees_[v] == 0) {
                    inDegreesQueue.push(v);
                }
            }
        }
        while (!outDegreesQueue.empty()) {
            int v = outDegreesQueue.front();
            outDegreesQueue.pop();
            for (int &u : invGraph_[v]) {
                if (--outDegrees_[u] == 0) {
                    outDegreesQueue.push(u);
                }
            }
        }
        int cnt = 0;  
        for (int i = 0; i < nodeCnt_; i++) {
            if (inDegrees_[i] == 0 ) {
                ++cnt;
                for (auto& v : Graph_[i]){
                    // if (!invGraph_[v].empty()){
                        auto it = find(invGraph_[v].begin(), invGraph_[v].end(),i);
                        invGraph_[v].erase(it);
                    // }
                }
                Graph_[i].clear();
            }
            if (outDegrees_[i] == 0 && inDegrees_[i] != 0) {
                ++cnt;
                for(auto &u : invGraph_[i]){
                    // if (!Graph_[u].empty()){
                        auto it = find(Graph_[u].begin(), Graph_[u].end(), i);
                        Graph_[u].erase(it);
                    // }
                }
                invGraph_[i].clear();
            }
        }
#ifdef DEBUG
        cout<<"出入度减枝，剪掉了："<<cnt<<"个节点"<<endl;
#endif
        return true;
    }

    void dfsForMultithread(int threadNo) {     // 第几个线程，线程编号,例如8个线程，则是0~7
		TicToc time;
        vector<bool> visited = vector<bool>(nodeCnt_, false);
        vector<int> visited1 = vector<int>(nodeCnt_, 0);
        vector<int> path;
		//vector<Path> ans[8];

        for (int i = 0; i < nodeCnt_; ++i) {
			if (i % THREADNUM != threadNo) {
				continue;
			}
            if (!Graph_[i].empty() && sccIds_[scc_[i]].size() > 2) {
                preDfs(invGraph_, i, i, 1, visited, visited1);
                for (auto x : invGraph_[i]) {
                    visited1[x] = -i - 1;
                }
                dfs(i, i, 1, path, ans_[threadNo], visited, visited1);
            }
        }
#ifdef DEBUG
		cout << "第 " << threadNo + 1 << "个线程DFS耗时：" << time.toc() * 1000 << " ms" << endl;
#endif 
    }

    void preDfs(const vector<vector<int>> &graph, int head, int cur, int depth, vector<bool> &visited, vector<int> &visited1) {
        for (auto &x : graph[cur]) {
            if (visited[x] || x < head) {
                continue;
            }
            visited1[x] = head;
            if (depth == 3) continue;
            visited[x] = 1;
            preDfs(graph, head, x, depth + 1, visited, visited1);
            visited[x] = 0;
        }
        return;
    }

    void dfs(int head, int cur, int depth, vector<int> &path, vector<Path>* pans, vector<bool>& visited, const vector<int>& visited1) {
        visited[cur] = true;
        path.push_back(cur);  
        auto &gCur = Graph_[cur];
        auto it = lower_bound(gCur.begin(), gCur.end(), head);
		for (; it != gCur.end(); ++it) {
			if (*it == head)
				continue;
			if (visited1[*it] == -(head+1) && !visited[*it]) {
				path.push_back(*it);
				if (path.size() > 2) {
					ansCnt_++;
					pans[depth + 1].emplace_back(Path(depth + 1, path));
				}
				path.pop_back();
			}
			
			if (depth < MAX_DEPTH - 1 ) {
				if (depth < 4) {
					if (visited[*it])
						continue;				
					dfs(head, *it, depth + 1, path, pans, visited, visited1);
				}
				else {
					// == -2的时候还需DFS
					if (visited[*it] || (visited1[*it] != head && visited1[*it] != -(head+1)))
						continue;
					dfs(head, *it, depth + 1, path, pans, visited, visited1);
				}
			}
		}
		visited[cur] = false;
		path.pop_back();

		return;
	}

    void tarjan(int root){
        static int top = -1;
        static int index = 0;

        if (dfn_[root] && Graph_[root].empty())        
            return;
        dfn_[root] = low_[root] = ++index;
        stack_[++top] = root;                          
        for ( auto &v: Graph_[root]){
            if (!dfn_[v]){                             
                tarjan(v);
                low_[root] = min(low_[root],low_[v]);  
            }
            else if (!scc_[v]){                        
                low_[root] = min(low_[root],dfn_[v]);
            }
        }
        if (low_[root] == dfn_[root]){                 
            ++sccnum_;
            while(true){
                int x = stack_[top--];
                scc_[x] = sccnum_;
                sccIds_[sccnum_].push_back(x);
                if (x == root)
                    break;
            }
        }
    }

    bool computeSccAndReduceBranch(){
        TicToc time;
        dfn_ = vector<int> (nodeCnt_,0);
        low_ = vector<int> (nodeCnt_,0);
        scc_ = vector<int> (nodeCnt_,0);
        stack_ = vector<int> (nodeCnt_);
        sccnum_ = 0;
        for (int i = 0; i<nodeCnt_; ++i){
            if (!Graph_[i].empty() && !dfn_[i]){
                tarjan(i);
            }
        }
#ifdef DEBUG
        cout << "求解连通分量用时：" << time.toc() << endl;
#endif
        // 对连通分量剪枝
        int branch_reduce_count = 0;
        auto p_sub_graph = sccIds_.begin();
        while (p_sub_graph != sccIds_.end()) {
            if (p_sub_graph->second.size() < 3){
                ++p_sub_graph;
                continue;
            } 
            for (auto &v : p_sub_graph->second) {
                if (Graph_[v].empty()) 
                    continue;
                for (auto iter = Graph_[v].begin(); iter != Graph_[v].end();) {
                    if (scc_[*iter] != p_sub_graph->first) {
                        iter = Graph_[v].erase(iter);
                        ++branch_reduce_count;
                    } else {
                        ++iter;
                    }
                }
                sort(Graph_[v].begin(), Graph_[v].end());
            }
            ++p_sub_graph;
        }
#ifdef DEBUG
        cout << "连通分量减枝：减掉：" << branch_reduce_count<<" 条边" << endl;
        cout << "连通分量减枝用时：" << time.toc() << endl;
#endif

#ifdef DEBUG1
        int count = 0;
        auto it = sccIds_.begin();
        while(it != sccIds_.end()){
            cout<<"第 "<<it->first<<" 个联通图的顶点数量是 "<<it->second.size()<<endl;
            if(it->second.size() > 2)
                ++count;
            ++it;
        }
        cout<<"连通子图顶点数大于2的数量："<<count<<",连通子图总数量："<<sccnum_<<endl;
#endif
        return true;
    }
};

int main(int argc, char **argv){
    TicToc totalTime;
    unordered_map<string,string> inputFiles;
    inputFiles["54"] = "./Dataset/54/test_data.txt";
    inputFiles["56"] = "./Dataset/56/test_data.txt";
    inputFiles["3738"] = "./Dataset/3738/test_data.txt";
    inputFiles["25910"] = "./Dataset/25910/test_data.txt";
    inputFiles["26571"] = "./Dataset/26571/test_data.txt";
    inputFiles["33705"] = "./Dataset/33705/test_data.txt";
    inputFiles["43278"] = "./Dataset/43278/test_data.txt";
    inputFiles["49945"] = "./Dataset/49945/test_data.txt";
    inputFiles["58284"] = "./Dataset/58284/test_data.txt";
    inputFiles["77409"] = "./Dataset/77409/test_data.txt";
    inputFiles["1004812"] = "./Dataset/1004812/test_data.txt";
    inputFiles["2861665"] = "./Dataset/2861665/test_data.txt";
    inputFiles["2896262"] = "./Dataset/2896262/test_data.txt";
    inputFiles["3512444"] = "./Dataset/3512444/test_data.txt";
    string outputFile = "./output_Baseline.txt";

    if (argc < 2){
        cout<<"请指定数据集，运行方式./test 54"<<endl;
        return 0;
    }
    DirectedGraph solveGraph(inputFiles[argv[1]], outputFile);

	TicToc time;
	solveGraph.parseInputFile();
	cout << "读取文件耗时：" << time.toc() << " s" << endl;

	solveGraph.constructGraph();
	cout << "建图耗时：" << time.toc() << " s" << endl;

	solveGraph.branchReduction();
	cout << "出度入度减枝耗时：" << time.toc() << " s" << endl;

	solveGraph.computeSccAndReduceBranch();
	cout << "强连通分量减枝耗时：" << time.toc() << " s" << endl;

	vector<thread> dfsObjs;
	for (int i = 0; i < THREADNUM; ++i) {
		dfsObjs.push_back(thread(&DirectedGraph::dfsForMultithread, &solveGraph, i));
	}
	for (auto it = dfsObjs.begin(); it < dfsObjs.end(); ++it) {
		it->join();
	}
	cout << THREADNUM << " 线程DFS耗时：" << time.toc() << " s" << endl;

	solveGraph.save_result_mmap();
	cout << "保存结果用时：" << time.toc() << " s" << endl;

    cout<<"程序用时："<<totalTime.toc()<<" s"<<endl;

    return 0;

}
