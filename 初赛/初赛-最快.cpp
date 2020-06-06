/**
 * @file 初赛-最快.cpp
 * @brief 取掉stl容器，最快速版本，需要凭借运气分配足够大的静态存储空间
 * @author ZHY
 * @version 8.0
 * @date 2020-04-24 23:30:58
 */
#include <vector>
#include <thread>
#include <sys/mman.h>
#include <sys/types.h>
#include <sys/stat.h>
#include <fcntl.h>
#include <unistd.h>
#include <string.h>
#include <stdlib.h>

#define THREADNUM 4
#define MAX_VERTEX_NUM 210000
#define INVALID_NUM 16843009
#define MAX_INDEGREE 30
#define MAX_OUTDEGREE 30

#define MAGIC 50000

using namespace std;

/* 工具函数 */
inline int intToChar(char *destStr, int val, bool comma_or_enter);
inline int charToint(char *string, int& len);
int compare (const void* a, const void* b);

/* 建图相关的变量 */
static int Graph_[MAX_VERTEX_NUM][MAX_OUTDEGREE];
static int invGraph_[MAX_VERTEX_NUM][MAX_INDEGREE];
static void* Graph_head = memset(Graph_, 1, sizeof(Graph_));
static void* invGraph_head = memset(invGraph_, 1, sizeof(Graph_));
static int inDegrees_[MAX_VERTEX_NUM] = { 0 };
static int outDegrees_[MAX_VERTEX_NUM] = { 0 };
static bool isTrueAccount_[MAX_VERTEX_NUM] = { false };     
static int maxNodeCnt_ = 0;    

/* 字符串相关的变量 */
static char accoutComma_[MAX_VERTEX_NUM][7];          
static int accountCommaLen_[MAX_VERTEX_NUM] = { 0 };

/* 保存结果相关 */
static int ans_3_[THREADNUM][500000 * 3];                
static int ans_4_[THREADNUM][500000 * 4];
static int ans_5_[THREADNUM][1000000 * 5];
static int ans_6_[THREADNUM][2000000 * 6];
static int ans_7_[THREADNUM][3000000 * 7];
static int threadOffset_[5] = { 500000 * 3, 500000 * 4, 1000000 * 5, 2000000 * 6, 3000000 * 7 };
static int* ansInt_[5] = { &ans_3_[0][0], &ans_4_[0][0], &ans_5_[0][0], &ans_6_[0][0], &ans_7_[0][0] };
static int threadIntLen_[THREADNUM][5] = { {0} };              
static int threadCharLen_[THREADNUM][5] = { {0} };               
static int ansCnt_[THREADNUM] = { 0 };      

static char ansBuf_[100*1024*1024];
/**
 * @brief 解析文件，并且建立邻接表，将帐号的字符串拷贝一份，保存为'帐号,'
 */
bool parseInputFileAndMap(char* inputFile) {
	struct stat sb;
	int fd = open(inputFile, O_RDONLY);
	fstat(fd, &sb);
	char *start = (char *)mmap(NULL, sb.st_size, PROT_READ, MAP_SHARED, fd, 0);
	register char* head = start;
	register int next = 0;
	register int i = 0, u, v;
	// 定义指向邻接表的指针
	int* pgraph[MAX_VERTEX_NUM] = { NULL };
	int* pinvgraph[MAX_VERTEX_NUM] = { NULL };
	for (int i = 0; i < MAX_VERTEX_NUM; ++i) {
		pgraph[i] = Graph_[i];
		pinvgraph[i] = invGraph_[i];
	}

	while (i < sb.st_size) {
		u = charToint(head, next);
		// 直接保存字符串，不需要int-->char[]了
		if (accountCommaLen_[u] == 0) {		
			memcpy(accoutComma_[u], head, next);
			accountCommaLen_[u] = next;
		}
		head += next;
		i += next;
		v = charToint(head, next);
		if (accountCommaLen_[v] == 0) {			
			memcpy(accoutComma_[v], head, next);
			accountCommaLen_[v] = next;
		}
		head += next;
		i += next;
		charToint(head, next);
		head += next;
		i += next;
		// 近似地获得账户的数量
		if (u >= MAGIC || v >= MAGIC) continue;
		isTrueAccount_[u] = true;
		isTrueAccount_[v] = true;
		if (max(u, v) > maxNodeCnt_) {
			maxNodeCnt_ = max(u, v);
		}
		// 建立邻接表
		*pgraph[u]++ = v;
		*pinvgraph[v]++ = u;
		++outDegrees_[u];
		++inDegrees_[v];
	}
	close(fd);
	munmap(start, sb.st_size);
	return true;
}

/**
 * @brief 把每层的结果memcpy到内存
 *
 * @param start 起始地址
 * @param layer 层数3~7
 */
void memcpyChar(char* dest, int layer) {
	register int offset = 0;
	register char* start = dest;
	int* head[THREADNUM];
	int* tail[THREADNUM];
	for (int i = 0; i < THREADNUM; ++i) {
		head[i] = ansInt_[layer - 3] + i * threadOffset_[layer - 3];
		tail[i] = head[i] + threadIntLen_[i][layer - 3];
	}
	for (unsigned int node = 0; node <= maxNodeCnt_; ++node) {
		if (!isTrueAccount_[node]) continue;
		unsigned int threadNo = node % THREADNUM;
		if (*head[threadNo] != node || head[threadNo] == tail[threadNo]) continue;
		while (*head[threadNo] == node) {
			for (int i = 0; i < layer; ++i) {
				int u = *(head[threadNo] + i);
				memcpy(start + offset, accoutComma_[u], accountCommaLen_[u]);
				offset += accountCommaLen_[u];
			}
			*(start + offset - 1) = '\n';
			head[threadNo] += layer;
			if (head[threadNo] >= tail[threadNo])
				break;
		}
	}
	return;
}

/**
 * @brief 多线程保存结果(未进行负载均衡)
 *
 * @param outputFile 输出文件路径
 */
void saveResult(char* outputFile) {
	int totalLoop = 0;                         // 环的数量
	int totalLayerCharNum[5] = { 0 };          // 每一层的字符数量
	int ansLen = 0;                            // 总字符数量
	for (int i = 0; i < THREADNUM; ++i) {
		totalLoop += ansCnt_[i];
		for (int j = 0; j < 5; ++j) {
			totalLayerCharNum[j] += threadCharLen_[i][j];
			ansLen += threadCharLen_[i][j];
		}
	}
	char buf[64];
	int lenOfTotalNum = intToChar(buf, totalLoop, false);
	ansLen += lenOfTotalNum;

	int fd = open(outputFile, O_CREAT | O_RDWR | O_TRUNC, 0666);
	intToChar(ansBuf_, totalLoop, false);


	int off = lenOfTotalNum;
	thread obj1(memcpyChar, ansBuf_ + off, 3);
	off += totalLayerCharNum[0];
	thread obj2(memcpyChar, ansBuf_ + off, 4);
	off += totalLayerCharNum[1];
	thread obj3(memcpyChar, ansBuf_ + off, 5);
	off += totalLayerCharNum[2];
	thread obj4(memcpyChar, ansBuf_ + off, 6);
	off += totalLayerCharNum[3];
	thread obj5(memcpyChar, ansBuf_ + off, 7);

	obj1.join();
	obj2.join();
	obj3.join();
	obj4.join();
	obj5.join();

	write(fd, ansBuf_, ansLen);
	close(fd);
}

/**
 * @brief 出度快速排序
 */
inline bool outDegreesQsort() {
	for (int i = 0; i <= maxNodeCnt_; ++i) {
		if (!isTrueAccount_[i]) continue;
		qsort(Graph_[i], outDegrees_[i], sizeof(Graph_[i][0]), compare);
	}
	return true;
}

/**
 * @brief 反向三层的DFS
 *
 * @param head 开始点
 * @param cur  当前点
 * @param depth 深度
 * @param visited 当前点是否被访问过
 * @param visited1 当前点是否可达开始点
 */
void preDfs(int head, int cur, int depth, bool* visited, int* visited1) {
	for (int i = 0; i < inDegrees_[cur]; ++i) {
		int u = invGraph_[cur][i];
		if (visited[u] || u < head) {
			continue;
		}
		visited1[u] = head;
		if (depth == 3) continue;
		visited[u] = 1;
		preDfs(head, u, depth + 1, visited, visited1);
		visited[u] = 0;

	}
	return;
}

/**
 * @brief 前向DFS
 *
 * @param head 开始点
 * @param cur  当前点
 * @param depth 深度
 * @param pathTail 指向存储路径的数组的尾指针
 * @param pathHead 指向存储路径的数组的头指针
 * @param visited 访问标记数组
 * @param visited1 逆3层可达标记数组
 * @param threadNo 第几个线程
 */
void dfs(int head, int cur, int depth, int* pathTail, int* pathHead, bool* visited, int* visited1, unsigned int threadNo) {
	visited[cur] = true;
	*pathTail++ = cur;
	for (int i = 0; i < outDegrees_[cur]; ++i) {
		int v = Graph_[cur][i];
		if (v < head)
			continue;
		if (v == head && visited[v]) {
			if (depth >= 3) {
				++ansCnt_[threadNo];
				memcpy(ansInt_[depth - 3] + threadNo * threadOffset_[depth - 3] + threadIntLen_[threadNo][depth - 3], pathHead, (depth) * sizeof(int));
				threadIntLen_[threadNo][depth - 3] += depth;
				// 记录字符串的长度，方便多进程写入(去掉6+1)
                for (int s = 0; s < depth; ++s) {
                    threadCharLen_[threadNo][depth - 3] += accountCommaLen_[*(pathHead + s)];
                }
   			}
		}

		if (depth < 7) {
			if (depth < 5) {
				if (visited[v])
					continue;
				dfs(head, v, depth + 1, pathTail, pathHead, visited, visited1, threadNo);
			}
			else {
				if (visited[v] || visited1[v] != head )
					continue;
				dfs(head, v, depth + 1, pathTail, pathHead, visited, visited1, threadNo);
			}
		}
	}
	visited[cur] = false;
	*(--pathTail) = INVALID_NUM;

	return;
}

/**
 * @brief 多线程DFS的入口函数
 *
 * @param threadNo 线程的编号，如4个线程，则是0~3
 */
void dfsForMultithread(unsigned int threadNo) {
	bool visited[maxNodeCnt_] = {0};
	int visited1[maxNodeCnt_] = {0};
	int path[8] = { INVALID_NUM };

	register int* pathTail = path;
	int* pathHead = path;

	for (unsigned int i = 0; i <= maxNodeCnt_; ++i) {
		if (i % THREADNUM != threadNo || !isTrueAccount_[i]) {
			continue;
		}
		if (outDegrees_[i] != 0 && inDegrees_[i] != 0) {
			preDfs(i, i, 1, visited, visited1);
			dfs(i, i, 1, pathTail, pathHead, visited, visited1, threadNo);
		}
	}
}

int main(int argc, char **argv){

	// char inputFile[64] = "/data/test_data.txt";
	// char outputFile[64] = "/projects/student/result.txt";
    char inputFile[128] = "./Dataset/1004812/test_data.txt";
    char outputFile[128] = "./output_array_5_5.txt";

	parseInputFileAndMap(inputFile);

	outDegreesQsort();

    vector<thread> dfsObjs;
    for (unsigned int i = 0; i < THREADNUM; ++i) {
        dfsObjs.push_back(thread(dfsForMultithread, i));
    }
	for (unsigned int i = 0; i < THREADNUM; ++i) {
		dfsObjs[i].join();
	}

	saveResult(outputFile);

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
int intToChar(char *destStr, int val, bool comma_or_enter) {
    static char index[]  = "0123456789";
    static char comma    = ',';
    static char lineFeed = '\n';
    static char endNull  = '\0';
    register int i = 0, len = 0;
    char *head, *end, tmp;
    do {
        destStr[i++] = index[val % 10];
        val /= 10;
        ++len;
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
 * @param len 转换后的字符串长度+1
 *
 * @return 转换后的int
 */
int charToint(char *string, int& len) {
    register int value = 0;
    len = 1;
    while (*string >= '0' && *string <= '9') {
        value *= 10;
        value += *string - '0';
        ++string;
        ++len;
    }
    if (*string != ',' && *string != '\r') value = 0;
    if (*string == '\r') ++len;
    return value;
}

/**
 * @brief qsort的升序排序比较函数
 */
int compare (const void* a, const void* b){
    return *(int*)a - *(int*)b;
}
