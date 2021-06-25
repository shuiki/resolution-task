#ifndef CONVERT_CLAUSE_H
#define CONVERT_CLAUSE_H
#include "convertTree.h"

extern bool variUsed[26];//标志量词用过的字母，从a开始
extern bool funcUsed[26];//标志函数用过的字母，主要从f开始
extern int clauseVariUsed[26];//标志子句里变量用过的字母



extern char concludeReflect[26];
const int notRelated = 0;
const int equal = 1;
const int opposite = 2;

const int ok = 0;
const int change = 1;

const int isNull = 2;

void first_del_arrow(LogicNode* root);
void second_del_neg(LogicNode* root);
void del_neg(LogicNode* root);
void third_var_regulation(LogicNode* root);
void fourth_del_exist(LogicNode* root, char* base, int baseNum, char* exist, int existNum,bool* exisUsed);
void fifth_mov_all(LogicNode* root, LogicNode* curNode);
void sixth_convert_cnf(LogicNode*& root);
void makeCalc(LogicNode* root, int& changeNum);
void calAll(LogicNode*& root, int& changeNum,bool isRoot=false);
bool mergeInNode(LogicNode* root,int& status,bool conclude=false);//消去重复的子节点，要求子节点全是叶子节点,返回是否有子节点剩下(false则整个节点删除)
int mergeBetweenNodes(LogicNode*& a,LogicNode*& b,bool conclude=false);//消去可以相互归结的子节点
int mergeRoot(LogicNode*& root,bool conclude=false);
int getRelation(LogicNode*& a, LogicNode*& b,bool conclude=false);
void seventh_del_all(LogicNode* root);
void ninth_clause_var_regu(LogicNode* root, char* u, int len);
bool belong_to_u(char c, char* u, int len);
void deal_exist(LogicNode*& root,char* u,int len);//归结公理结束后，即将进行推理时调用,u为全集，把之前用大写字母和函数标志的存在符号用全集中个体替换
#endif