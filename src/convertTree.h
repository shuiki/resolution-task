#ifndef CONVERT_TREE_H
#define CONVERT_TREE_H
#include<queue>
#include<iostream>

typedef struct {
	char type;
	char var;
} Qualifier;


const int TEXTLEN=30;
static bool variUsed[26];//标志量词用过的字母，从a开始
static bool funcUsed[26];//标志函数用过的字母，主要从f开始
//static bool exisUsed[26];//存在量词替换用过的字母
static int clauseVariUsed[26];//子句变量用过的字母
static char reflect[26];

struct LogicNode {
	Qualifier qualifiers[10] = { 0 };//量词情况
	int quaNum = 0;//量词数目
	bool isLeaf = true;//是否原子语句
	bool antiFlag = false;//是否有非符号
	bool emptyFlag = false;//是空结点
	char name[TEXTLEN] = { 0 };//语句名，Q(x)中的Q
	int nameLen = 0;
	char vars[TEXTLEN] = { 0 };//参数表
	int varsNum = 0;
	LogicNode* child = nullptr;
	LogicNode* brother = nullptr;
	char broLink = '\0';//与兄弟的连接符
};
//root为empty条件
//!quaNum&&!isLeaf&&!antiFlag&&!nameLen&&!varsNum&&!root->child->isLeaf


const int Letter = 0;
const int Qualif = 1;
const int Linker = 2;
const int Unknown = 3;

bool isLetter(char c);
bool isUpper(char c);
bool isLower(char c); 
int getType(char c);
LogicNode* createNode(char* str, int len, int& pos,int thisIndex,int& curIndex,bool conti, bool isQuialNode=false);
//thisIndex: 有几个量词，curIndex:几个量词没完成，conti:是否属于连续的量词，isQuialNode:是否是量词作用域节点（量词后第一个括号）
LogicNode* strToTree(char* str, int len);
int formRead(wchar_t* a, char* str,bool*exisUsed=NULL);
void showNode(LogicNode* root, char* str, int& pos);
int treeToStr(LogicNode* root, char* str);
LogicNode* copyTree(LogicNode* root,bool isRoot=true);
LogicNode* copyNode(LogicNode* root);
void settleTree(LogicNode* root, LogicNode* front, bool parentFlag, char depLink,char* concludeReflect);//整理树，返回标准化的新树，把同一运算都放在同一层

//parent是root的前驱节点 deplink是root所在层的运算符号
LogicNode* collectUsefulNodes(LogicNode* root,char link='\0');//清除无用节点
void letLeafFirst(LogicNode* root,LogicNode* parent);
void deleteTree(LogicNode* root);
int showTree(LogicNode* root, bool showClause = false);
void adjustTree(LogicNode*& root);//直接被main调用的函数
wchar_t corre(char c);
//LogicNode* copyTreeWithoutBro(LogicNode* root);
#endif 