#include"convertClause.h"

char concludeReflect[26] = { 0 };//小写任意变量映射到大写实体



void first_del_arrow(LogicNode* root)
{
	if (!root)
		return;
	if (root->child&&root->child->broLink == '$')//双箭头
	{
		LogicNode* a = copyTree(root->child);//a<->b
		LogicNode* b = copyTree(root->child->brother);
		LogicNode* nextBro = root->child->brother->brother;
		char c = root->child->brother->broLink;
		LogicNode* top = new LogicNode;
		LogicNode* upper1 = new LogicNode;//a->b的上层节点
		LogicNode* upper2 = new LogicNode;//b->a的上层节点
		top->isLeaf = false;
		upper1->isLeaf = false;
		upper2->isLeaf = false;
		upper1->brother = upper2;
		upper1->broLink = '*';
		upper1->child = root->child;
		root->child = top;
		upper1->child->antiFlag = !upper1->child->antiFlag;
		upper1->child->broLink = '+';
		upper2->child = a;
		a->brother = b;
		a->broLink = '+';
		b->antiFlag = !b->antiFlag;
		top->child = upper1;
		top->brother = nextBro;
		top->broLink = c;
	}
	first_del_arrow(root->child);
	if (root->broLink == '-')//单箭头
	{
		root->antiFlag = !root->antiFlag;
		root->broLink = '+';
	}
	first_del_arrow(root->brother);
	//if (!root->quaNum && !root->isLeaf && !root->antiFlag && !root->nameLen && !root->varsNum && (root->child&&(!root->child->isLeaf||!root->child->brother)))
		//root->emptyFlag = true;
}

void second_del_neg(LogicNode* root)
{
	del_neg(root);
}



void del_neg(LogicNode* root)
{
	if (!root)
		return;
	LogicNode* pointer;
	if (root->antiFlag && root->child)
	{
		root->antiFlag = false;
		pointer = root;
		if (pointer->quaNum > 0)
		{
			for (int i = 0; i < pointer->quaNum; i++)
			{
				pointer->qualifiers[i].type = pointer->qualifiers[i].type == '@' ? '#' :
					pointer->qualifiers[i].type == '#' ? '@' : pointer->qualifiers[i].type;
			}
		}
		pointer = pointer->child;
		while (pointer)
		{
			pointer->antiFlag = !pointer->antiFlag;
			pointer->broLink = pointer->broLink == '+' ? '*' : pointer->broLink == '*' ? '+' : pointer->broLink;
			pointer = pointer->brother;
		}
	}
	if (root->brother)
		del_neg(root->brother);
	del_neg(root->child);
	//if (!root->quaNum && !root->isLeaf && !root->antiFlag && !root->nameLen && !root->varsNum && (root->child && (!root->child->isLeaf || !root->child->brother)))
		//root->emptyFlag = true;
}

//!((#x)(@y)(#z)(A*B)+(@t)(#s)(C+D))

void changeVari(LogicNode* root, char ori, char nex)//把量词节点下所有为ori的量词都换成nex
{
	if (!root)
		return;
	if (root->isLeaf)
	{
		for (int i = 0; i < root->varsNum; i++)
		{
			if (root->vars[i] == ori)
				root->vars[i] = nex;
		}
		changeVari(root->brother, ori, nex);
		return;
	}
	changeVari(root->child, ori, nex);
	changeVari(root->brother,ori,nex);
}

void third_var_regulation(LogicNode* root)
{
	if (!root)
		return;
	if (root->quaNum > 0)
	{
		for (int i = 0; i < root->quaNum; i++)
		{
			if (variUsed[root->qualifiers[i].var - 'a'])//量词已被占用
			{
				int j;
				for (j = 0; variUsed[j]; j++);
				char n = (char)j + 'a';
				changeVari(root, root->qualifiers[i].var, n);
				root->qualifiers[i].var = n;
			}
			else 
			{
				variUsed[root->qualifiers[i].var - 'a'] = true;
			}
		}
	}
	third_var_regulation(root->child);
	third_var_regulation(root->brother);
	//if (!root->quaNum && !root->isLeaf && !root->antiFlag && !root->nameLen && !root->varsNum && (root->child && (!root->child->isLeaf || !root->child->brother)))
		//root->emptyFlag = true;
}

void fourth_del_exist(LogicNode* root, char* base, int baseNum, char* exist, int existNum,bool*exisUsed)
{
	if (!root)
		return;
	if (root->quaNum > 0&&root->qualifiers[0].type=='#')//任意量词节点
	{
		base[baseNum] = root->qualifiers[0].var;
		fourth_del_exist(root->child, base, baseNum + 1, exist, existNum,exisUsed);
		fourth_del_exist(root->brother, base, baseNum, exist, existNum,exisUsed);
	}
	else if (root->quaNum > 0 && root->qualifiers[0].type == '@')//存在量词节点
	{
		exist[existNum] = root->qualifiers[0].var;
		root->qualifiers[0].type = '\0';
		root->qualifiers[0].var = '\0';
		root->quaNum = 0;
		//root->emptyFlag = true;
		fourth_del_exist(root->child, base, baseNum, exist, existNum + 1,exisUsed);
		fourth_del_exist(root->brother, base, baseNum, exist, existNum,exisUsed);
	}
	else//普通节点
	{
		if (root->isLeaf)
		{
			char temp[TEXTLEN] = { 0 };
			bool exiFlag = false;
			int tempPos=0;
			for (int i = 0; i < root->varsNum; i++)
			{
				exiFlag = false;
				for (int j = 0; j < existNum; j++)
				{
					if (exist[j] == root->vars[i])
					{
						exiFlag = true;//是存在量词下辖变量
						break;
					}
				}
				if (exiFlag)
				{
					if (baseNum != 0)//在任意量词下
					{
						char c = 'f';
						while (funcUsed[c - 'a'])
							c++;
						temp[tempPos++] = c;
						temp[tempPos++] = '(';
						for (int j = 0; j < baseNum; j++)
						{
							temp[tempPos++] = base[j];
							temp[tempPos++] = ',';
						}
						temp[--tempPos] = ')';
						tempPos++;
						funcUsed[c - 'a'] = true;
					}
					else
					{
						char c = 'A';
						while (exisUsed[c - 'A'])
						{
							c = c + 1;
						}
						temp[tempPos++] = c;
						exisUsed[c - 'A'] = true;
					}
				}
				else
				{
					temp[tempPos++] = root->vars[i];
				}
			}
			for (int k = 0; k < TEXTLEN; k++)
			{
				root->vars[k] = temp[k];
			}
		}
		else
		{
			fourth_del_exist(root->child, base, baseNum, exist, existNum,exisUsed);
		}
		fourth_del_exist(root->brother, base, baseNum, exist, existNum,exisUsed);
	}
	//if (!root->quaNum && !root->isLeaf && !root->antiFlag && !root->nameLen && !root->varsNum && (root->child && (!root->child->isLeaf || !root->child->brother)))
		//root->emptyFlag = true;
}

void fifth_mov_all(LogicNode* root, LogicNode* curNode)//左移全称量词
{
	if (!root || !curNode)
		return;
	if (curNode->quaNum > 0)
	{
		root->emptyFlag = false;
		for (int i = 0; i < curNode->quaNum; i++)
		{
			root->qualifiers[root->quaNum++] = curNode->qualifiers[i];
			curNode->qualifiers[i] = { '\0','\0' };
		}
		curNode->quaNum = 0;
		//if (!curNode->child->isLeaf || !curNode->child->brother)
			//curNode->emptyFlag = true;
	}
	fifth_mov_all(root, curNode->child);
	fifth_mov_all(root, curNode->brother);
	//if (!root->quaNum && !root->isLeaf && !root->antiFlag && !root->nameLen && !root->varsNum && (root->child && (!root->child->isLeaf || !root->child->brother)))
		//root->emptyFlag = true;
}

void sixth_convert_cnf(LogicNode*& root)
{
	int changeNum = 1;
	LogicNode* nRoot;
	if (root->child&&root->child->broLink == '+')
	{
		LogicNode* mid = new LogicNode;
		mid->isLeaf = false;
		mid->child = root->child;
		root->child = mid;
	}
	while (changeNum)
	{
		changeNum = 0;
		calAll(root, changeNum,true);
	}
	root = collectUsefulNodes(root);
	nRoot = root;
	if (root->brother)
	{
		root = new LogicNode;
		root->child = nRoot;
		root->isLeaf = false;
		root->emptyFlag = true;
	}
	if (!root->quaNum)
		root->emptyFlag = true;
	if (root->quaNum && root->child && !root->child->brother && !root->child->isLeaf)
	{
		nRoot = root->child->child;
		delete root->child;
		root->child = nRoot;
	}
	settleTree(root, nullptr, false, '\0',concludeReflect);
}

void calAll(LogicNode*& root, int& changeNum,bool isRoot)
{
	if (!root)
		return;
	calAll(root->child, changeNum);
	int i = changeNum;
	makeCalc(root, changeNum);
	if (changeNum > i)
	{
		//root = collectUsefulNodes(root);
		LogicNode* nRoot = root;
		if (root->brother && isRoot)
		{
			root = copyNode(nRoot);
			root->child = nRoot->brother;
			root->broLink = '\0';
			delete nRoot;
		}
		settleTree(root, nullptr, false, '\0', concludeReflect);
		letLeafFirst(root, nullptr);
	}
	calAll(root->brother, changeNum);
}

void makeCalc(LogicNode* root, int& changeNum)
{
	LogicNode* calTar=nullptr, * broStart=nullptr, * curBro=nullptr, * broPointer=nullptr, * p, * q;
	LogicNode* front=root;
	LogicNode* evenNode=nullptr;
	LogicNode* lastNode=nullptr;
	int antiLeafLeft = 0;
	LogicNode* calFront = root;//calTar的前驱节点
	bool parentFlag=true;//calTar前驱类型
	while (front->brother)
		front = front->brother;
	if (root->child && root->child->broLink == '+')
	{
		calTar = root->child;
		lastNode = root->child;
		while (lastNode->brother)//补上一个复制的第一个子节点，让最后不会剩余一个非叶子节点没被计算
		{
			if (lastNode->isLeaf)
				antiLeafLeft++;
			else
			{
				if (antiLeafLeft > 0)
					antiLeafLeft--;
				else
					antiLeafLeft = antiLeafLeft == 0 ? -1 : 0;
			}
			lastNode = lastNode->brother;
		}
		if (antiLeafLeft > 0)
			antiLeafLeft--;
		else
			antiLeafLeft = antiLeafLeft == 0 ? -1 : 0;
		if (antiLeafLeft == -1)
		{
			evenNode = copyTree(calTar);
			lastNode->brother = evenNode;
			evenNode->broLink = '\0';
			evenNode->brother = nullptr;
			lastNode->broLink = '+';
		}
		while (calTar->brother && calTar->brother->isLeaf)
		{
			calFront = calTar;
			parentFlag = false;
			calTar = calTar->brother;
		}
		if (!calTar->brother)
			return;
		changeNum++;
		if (calTar->isLeaf)//P∨（Q∧R）=（P∨Q）∧（P∨R）
		{
			broPointer = calTar->brother->child;
			while (broPointer)
			{
				p = new LogicNode;
				p->isLeaf = false;
				if (curBro)
				{
					curBro->broLink = '*';
					curBro->brother = p;
				}
				curBro = p;
				if (broPointer == calTar->brother->child)
					broStart = p;
				p->child = copyNode(calTar);
				p->child->broLink = '+';
				p->child->brother = copyTree(broPointer);
				broPointer = broPointer->brother;
			}
		}
		else//（A∧B）∨（C∧D）= (A∨（C∧D）)∧(B∨（C∧D）)
		{
			q = calTar->brother;
			broPointer = calTar->child;
			while (broPointer)
			{
				p = new LogicNode;
				p->isLeaf = false;
				if (curBro)
				{
					curBro->broLink = '*';
					curBro->brother = p;
				}
				curBro = p;
				if (broPointer == calTar->child)
					broStart = p;
				p->child = copyTree(broPointer);
				p->child->broLink = '+';
				p->child->brother = copyTree(q);
				broPointer = broPointer->brother;
			}
			
		}
		if (parentFlag)
		{
			calFront->child = calTar->brother->brother;
		}
		else
		{
			calFront->brother = calTar->brother->brother;
		}
		delete calTar->brother;
		delete calTar;
		while (front->brother)
			front = front->brother;
		front->brother = broStart;
		front->broLink = '*';
	}
}

int getRelation(LogicNode*& a, LogicNode*& b,bool conclude)//叶子节点
{
	if (a->nameLen != b->nameLen || a->varsNum != b->varsNum)
		return notRelated;
	for (int i = 0; i < a->nameLen; i++)
	{
		if (a->name[i] != b->name[i])
			return notRelated;
	}
	char tempA[TEXTLEN] = { 0 };
	char tempB[TEXTLEN] = { 0 };
	int varLenA = 0;
	int varLenB = 0;
	int posA = 0;
	int posB = 0;
	bool concludeOK=false;
	for (int i = 0; i < a->varsNum; i++)
	{
		varLenA = 0;
		if (a->vars[posA + 1] != '(')
		{
			if (isLower(a->vars[posA]) && concludeReflect[a->vars[posA] - 'a'])
				a->vars[posA] = concludeReflect[a->vars[posA] - 'a'];
			varLenA = 1;
			tempA[0] = a->vars[posA++];
		}
		else
		{
			while (a->vars[posA] != ')')
			{
				if (isLower(a->vars[posA]) && concludeReflect[a->vars[posA] - 'a'])
					a->vars[posA] = concludeReflect[a->vars[posA] - 'a'];
				tempA[varLenA++] = a->vars[posA++];
			}
			tempA[varLenA++] = a->vars[posA++];
		}
		int j;
		for (j = 0; j < b->varsNum; j++)
		{
			varLenB = 0;
			if (b->vars[posB + 1] != '(')
			{
				if (isLower(b->vars[posB]) && concludeReflect[b->vars[posB] - 'a'])
					b->vars[posB] = concludeReflect[b->vars[posB] - 'a'];
				varLenB = 1;
				tempB[0] = b->vars[posB++];
			}
			else
			{
				while (a->vars[posB] != ')')
				{
					if (isLower(b->vars[posB]) && concludeReflect[b->vars[posB] - 'a'])
						b->vars[posB] = concludeReflect[b->vars[posB] - 'a'];
					tempB[varLenB++] = b->vars[posB++];
				}
				tempB[varLenB++] = b->vars[posB++];
			}
			int t;
			concludeOK = false;
			for (t = 0; t < varLenA; t++)
			{
				if (conclude && (!(isUpper(tempA[0])&&isUpper(tempB[0]))))
				{
					if (isUpper(tempA[0]))
						concludeReflect[tempB[0] - 'a'] = tempA[0];
					else if(isUpper(tempB[0]))
						concludeReflect[tempA[0] - 'a'] = tempB[0];
					concludeOK = true;
					break;
				}
				else if (tempA[t] != tempB[t])
					break;
			}
			if (t == varLenA||concludeOK)
				break;
		}
		if (j == b->varsNum)
			return notRelated;
	}
	if (a->antiFlag == b->antiFlag)
		return equal;
	return opposite;
}



bool mergeInNode(LogicNode* root,int&status,bool conclude)
{
	if (!root||!root->child)
		return false;
	LogicNode* curChild=root->child;
	LogicNode* curFront = root;
	bool parentFlag = true;
	bool delFlag = false;
	LogicNode* compChild = root->child->brother;
	LogicNode* compFront = root->child;//comp的前驱兄弟
	LogicNode* curNext;
	char c = curChild->broLink;
	while (curChild) 
	{
		if (curChild->emptyFlag)
		{
			curFront = curChild;
			curChild = curChild->brother;
			parentFlag = false;
			continue;
		}
		delFlag = false;
		compChild = curChild->brother;
		compFront = curChild;
		while (compChild)
		{
			if(compChild->emptyFlag)
			{
				compFront = compChild;
				compChild = compChild->brother;
				continue;
			}
			if (curChild->isLeaf && compChild->isLeaf)
			{
				int relation = getRelation(compChild, curChild,conclude);
				if (relation == equal)
				{
					compFront->brother = compChild->brother;
					compFront->broLink = compChild->broLink;
					delete compChild;
					compChild = compFront->brother;
					status = change;
				}
				else if (relation == opposite)
				{
					if (c == '*')
					{
						status = isNull;
						return true;
					}
					status = change;
					curNext = compChild == curChild->brother ? compChild->brother : curChild->brother;
					if (parentFlag)
						curFront->child = curNext;
					else
						curFront->brother = curNext;
					curChild->brother = curNext;
					if (!curNext)
					{
						if(!parentFlag)
							curFront->broLink = '\0';
						//else
						//{
							//root->child = nullptr;
							//root->emptyFlag = true;
							//delete compChild;
							//delete curChild;
							//return false;
						//}
					}
					if (compChild&&compFront != curChild)
					{
						compFront->brother = compChild->brother;
						compFront->broLink = compChild->broLink;
					}
					else
					{
						if (!parentFlag)
							compFront = curFront->brother;
						else
							compFront = curFront->child;
					}
					deleteTree(compChild);
					delFlag = true;
					if (compFront)
						compChild = compFront->brother;
					else
						compChild = nullptr;
				}
				else 
				{
					compFront = compChild;
					if (compChild)
						compChild = compChild->brother;
				}
			}
			else if(compChild)
				compChild = compChild->brother;
		}
		if (delFlag)
		{
			if (curChild->brother)
			{
				if (parentFlag)
					curFront->child = curChild->brother;
				else
				{
					curFront->brother = curChild->brother;
					curFront->broLink = curChild->broLink;
				}
			}
			deleteTree(curChild);
			curChild = parentFlag ? curFront->child : curFront->brother;
			delFlag = false;
		}
		else
		{
			curFront = curChild;
			curChild = curChild->brother;
			parentFlag = false;
		}
	}
	curFront->broLink = '\0';
	if (root->child && root->child->isLeaf && !root->child->brother)
	{
		root->antiFlag = root->child->antiFlag;
		root->isLeaf = true;
		for (int i = 0; i < TEXTLEN; i++)
		{
			root->name[i] = root->child->name[i];
			root->vars[i] = root->child->vars[i];
		}
		for (int i = 0; i < 10; i++)
			root->qualifiers[i] = root->child->qualifiers[i];
		root->quaNum = root->child->quaNum;
		root->nameLen = root->child->nameLen;
		root->varsNum = root->child->varsNum;
		root->emptyFlag = root->child->emptyFlag;
		root->child = nullptr;
		return true;
	}
	if (root->child)
		return true;
	else
		return false;
}

int mergeBetweenNodes(LogicNode*& a,LogicNode*& b,bool conclude)
{
	if (!a || !b)
		return ok;
	LogicNode* compChild, * compFront;
	bool parentFlag;
	if (a->isLeaf && b->isLeaf)
		return ok;
	if (a->emptyFlag || b->emptyFlag)
		return ok;
	else if (!a->isLeaf && !b->isLeaf)//都不是叶子节点，判断是否一个中包含另一个的全部子节点
	{
		LogicNode* achild=a->child, * bchild=b->child;
		int aNum=0, bNum=0;
		while (achild)
		{
			aNum++;
			achild = achild->brother;
		}
		while (bchild)
		{
			bNum++;
			bchild = bchild->brother;
		}
		if (!aNum||!bNum)
			return ok;
		LogicNode* less = aNum > bNum ? b : a;
		LogicNode* more = aNum > bNum ? a : b;
		LogicNode* lchild = less->child;
		LogicNode* mchild = more->child;
		bool noFlag = false;
		bool nullFlag = false;
		for (int m = 0; m < 2; m++)
		{
			lchild = less->child;
			mchild = more->child;
			while (lchild)
			{
				if (!lchild->emptyFlag)
				{
					mchild = more->child;
					while (mchild)
					{
						if (!mchild->emptyFlag)
						{
							int relation = getRelation(lchild, mchild, conclude);
							if (relation == notRelated)
								noFlag = true;
							//else if (relation == !opposite)
								//nullFlag = true;
							//return isnull;
							else if (relation == equal)
							{
								noFlag = false;
								if (m == 1)
									mchild->emptyFlag = true;
								break;
							}
						}
						mchild = mchild->brother;
					}
				}
				lchild = lchild->brother;
				if (noFlag)
					return ok;
			}
		}
		//return more == a ? aout : bout;
		return change;
	}
	LogicNode* leaf, * other;
	leaf = a->isLeaf ? a : b;
	other = a->isLeaf ? b : a;
	compChild = other->child;
	compFront = other;
	parentFlag = true;
	while (compChild)
	{
		if (!compChild->emptyFlag)
		{
			int relation = getRelation(leaf, compChild, conclude);
			if (relation == equal && !compChild->emptyFlag)
			{
				compChild->emptyFlag = true;
				//return leaf == a ? bout : aout;
				return change;
			}
			else if (relation == opposite)
			{
				if (parentFlag)
					compFront->child = compChild->brother;
				else
				{
					compFront->brother = compChild->brother;
					compFront->broLink = compChild->broLink;
				}
				delete compChild;
				return change;
			}
		}
		compFront = compChild;
		compChild = compChild->brother;
		parentFlag = false;
	}
	return ok;
}
//(#x)(f(x,y)-g(x,y))*f(A,B)
int mergeRoot(LogicNode*& root,bool conclude)
{
	int status = change;
	while (status == change)
	{
		adjustTree(root);
		status = ok;
		if (!mergeInNode(root, status,conclude))
			return isNull;
		if (status == isNull)
			return isNull;
		LogicNode* mergeTar, * tarFront, * mergeComp, * compFront;
		bool parentFlag = true;
		mergeComp = root->child;
		compFront = root;
		while (mergeComp)
		{
			if (!mergeInNode(mergeComp, status,conclude))
			{
				if (parentFlag)
					compFront->child = mergeComp;
				else
					compFront->brother = mergeComp;
				if (status == isNull)
					return isNull;
			}
			compFront = mergeComp;
			mergeComp = mergeComp->brother;
			parentFlag = false;
		}
		//showTree(root);
		mergeTar = root->child;
		mergeComp = mergeTar->brother;
		compFront = mergeTar;
		tarFront = root;
		parentFlag = true;
		bool tarDel = false;
		int result;
		while (mergeTar)
		{
			settleTree(root, nullptr, false, '\0', concludeReflect);
			if (mergeTar->emptyFlag)
			{
				tarFront = mergeTar;
				mergeTar = mergeTar->brother;
				parentFlag = false;
				continue;
			}
			tarDel = false;
			mergeComp = mergeTar->brother;
			compFront = mergeTar;
			while (mergeComp)
			{
				settleTree(root, nullptr, false, '\0', concludeReflect);
				if (mergeComp->emptyFlag)
				{
					compFront = mergeComp;
					mergeComp = mergeComp->brother;
					continue;
				}
				result = mergeBetweenNodes(mergeTar, mergeComp, conclude);
				if (result == change)
					status = change;
				compFront = mergeComp;
				mergeComp = mergeComp->brother;
			}
			if (tarDel)
			{
				mergeTar = parentFlag ? tarFront->child : tarFront->brother;
			}
			else
			{
				tarFront = mergeTar;
				mergeTar = mergeTar->brother;
				parentFlag = false;
			}
		}
		tarFront->broLink = '\0';
		//清理无用节点
		//showTree(root);
		//adjustTree(root);
		LogicNode* nRoot;
		root = collectUsefulNodes(root);
		nRoot = root;
		if (!root || root->brother)
		{
			root = new LogicNode;
			root->child = nRoot;
			root->isLeaf = false;
			root->emptyFlag = true;
		}
		if (!root->quaNum)
			root->emptyFlag = true;
		if (root->quaNum && root->child && !root->child->brother && !root->child->isLeaf)
		{
			nRoot = root->child->child;
			delete root->child;
			root->child = nRoot;
		}
		settleTree(root, nullptr, false, '\0', concludeReflect);
		//showTree(root);
	}
	for (int i = 0; i < 26; i++)
	{
		concludeReflect[i] = 0;
	}
	return ok;
}
/*		LogicNode* nRoot;
		root = collectUsefulNodes(root);
		nRoot = root;
		if (!root || root->brother)
		{
			root = new LogicNode;
			root->child = nRoot;
			root->isLeaf = false;
			root->emptyFlag = true;
		}
		if (!root->quaNum)
			root->emptyFlag = true;
		if (root->quaNum && root->child && !root->child->brother && !root->child->isLeaf)
		{
			nRoot = root->child->child;
			delete root->child;
			root->child = nRoot;
		}
		settleTree(root, nullptr, false, '\0');
		*/

void seventh_del_all(LogicNode* root)
{
	for (int i = 0; i < root->quaNum; i++)
		root->qualifiers[i] = { 0,0 };
	root->quaNum = 0;
	root->emptyFlag = true;
	root->isLeaf = false;
}

void ninth_clause_var_regu(LogicNode* root,char* u,int len)
{
	LogicNode* clause = root->child;
	LogicNode*leaf;
	int tag = 1;
	while (clause)
	{
		for (int i = 0; i < 26; i++)
			reflect[i] = 0;
		if (clause->isLeaf)
		{
			for (int i = 0; i < TEXTLEN; i++)
			{
				char c = clause->vars[i];
				if (belong_to_u(c, u, len))
					continue;
				if (isLetter(c) && !clauseVariUsed[c - 'a'])
					clauseVariUsed[c - 'a'] = tag;
				else if (isLetter(c) && clauseVariUsed[c - 'a'] < tag)
				{
					char t = 'a';
					while (t - 'a' < 26 && clauseVariUsed[t - 'a'])
						t++;
					for (int j = i; j < TEXTLEN; j++)
						if (clause->vars[j] == c)
							clause->vars[j] = t;
					clauseVariUsed[t - 'a'] = tag;
				}
			}
		}
		else
		{
			leaf = clause->child;
			while (leaf)
			{
				for (int i = 0; i < TEXTLEN; i++)
				{
					char c = leaf->vars[i];
					if (belong_to_u(c, u, len))
						continue;
					if (isLetter(c) && !clauseVariUsed[c - 'a'])
						clauseVariUsed[c - 'a'] = tag;
					else if (isLetter(c) && clauseVariUsed[c - 'a'] < tag)
					{
						char t = 'a';
						if (reflect[c - 'a'])
							t = reflect[c - 'a'];
						else 
						{
							while (t - 'a' < 26 && clauseVariUsed[t - 'a'])
								t++;
						}
						for (int j = i; j < TEXTLEN; j++)
							if (leaf->vars[j] == c)
								leaf->vars[j] = t;
						reflect[c - 'a'] = t;
						clauseVariUsed[t - 'a'] = tag;
					}
				}
				leaf = leaf->brother;
			}
		}
		clause = clause->brother;
		tag++;
	}
}

bool belong_to_u(char c, char* u, int len)
{
	if (!len)
		return true;
	for (int i = 0; i < len; i++)
		if (u[i] == c)
			return true;
	return false;
}

void deal_exist(LogicNode*& root, char* u,int len)
{
	if (!root)
		return;
	if (root->isLeaf)
	{ 
		for (int i = 0; i < TEXTLEN; i++)
		{
			if (isUpper(root->vars[i]) && !belong_to_u(root->vars[i], u, len))//单个存在字符
			{
				LogicNode* firstBro=nullptr;
				LogicNode* curBro=nullptr, * temp=nullptr;
				for (int j = 0; j < len; j++)
				{
					temp = copyTree(root);
					temp->vars[i] = u[j];
					if (j == 0)
					{
						firstBro = temp;
						curBro = temp;
					}
					else
					{
						curBro->broLink = '+';
						curBro->brother = temp;
						curBro = temp;
					}
				}
				root->child = firstBro;
				root->isLeaf = false;
				for (int i = 0; i < TEXTLEN; i++)
				{
					root->vars[i] = 0;
					root->name[i] = 0;
				}
				root->nameLen = 0;
				root->varsNum = 0;
				deal_exist(root, u, len);
				deal_exist(root->brother, u, len);
				return;
			}
			else if(root->vars[i+1]=='(')
			{
				char c = 'A';
				while (belong_to_u(c, u, len))
					c++;
				root->vars[i] = c;
				int front=i+1, back=i+1;
				while (root->vars[back] != ')')
					back++;
				back++;
				while (back < TEXTLEN)
					root->vars[front++] = root->vars[back++];
				while (front < TEXTLEN)
					root->vars[front++] = 0;
				deal_exist(root, u, len);
				return;
			}
		}
		deal_exist(root->brother, u, len);
		return;
	}
	else
	{
		deal_exist(root->child, u, len);
		deal_exist(root->brother, u, len);
		return;
	}
	
}


