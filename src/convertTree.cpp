#include"convertTree.h"
#include<ctype.h>

bool isLetter(char c)
{
	return ((c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'z'));
}

bool isUpper(char c)
{
	return c >= 'A' && c <= 'Z';
}

bool isLower(char c)
{
	return c >= 'a' && c <= 'z';
}

int getType(char c)
{
	if ((c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'z'))
		return Letter;
	switch (c) {
	case('$'):
	case('-'):
	case('!'):
	case('*'):
	case('+'):
		return Linker;
	case('@'):
	case('#'):
		return Qualif;
	default:
		return Unknown;
	}
}

LogicNode* createNode(char* str, int len, int& pos,int thisIndex,int& curIndex,bool conti, bool isQuialNode)
{
	if (pos >= len)
		return nullptr;
	char curRead = str[pos];
	if (curRead == ')')
		return nullptr;
	LogicNode* curNode = new LogicNode;
	bool IsQuialNode = isQuialNode;
	if (curRead == '!')
	{
		curNode->antiFlag = true;
		pos++;
		curRead = str[pos];
	}
	if (isLetter(curRead))//读Q(x,y)这种
	{
		while (isLetter(str[pos]))
		{
			curNode->name[curNode->nameLen++] = str[pos++];
		}
		funcUsed[tolower(curNode->name[0]) - 'a'] = true;
		if (str[pos] == '(')
		{
			while (str[pos] != ')')
			{
				pos++;
				if (isLetter(str[pos]))
				{
					curNode->vars[curNode->varsNum++] = str[pos];
				}
			}
			pos++;
		}
		if (getType(str[pos]) == Linker)
		{
			curNode->broLink = str[pos];
			pos++;
			curNode->brother = createNode(str, len, pos,thisIndex,curIndex,conti);
		}
		if (isQuialNode)
			curIndex--;
	}
	else if (curRead == '(')
	{
		bool isQual = false;
		bool nextIsQual = false;
		curNode->isLeaf = false;
		if (str[pos + 1] == '!' && getType(str[pos + 3]) == Qualif)
		{
			curNode->antiFlag = true;
			pos += 2;
			curNode->child = createNode(str, len, pos,thisIndex,curIndex,conti);
		}
		else
		{
			bool isConti = conti;
			if(getType(str[pos + 1]) == Qualif)
			{
				isQual = true;
				nextIsQual = isQuialNode;
				if (isConti)
					nextIsQual = true;
				curNode->qualifiers[curNode->quaNum++] = { str[pos + 1],str[pos + 2] };//赋值量词
				pos += 4;
				if (getType(str[pos + 1]) == Qualif)
					isConti = true;
			}
			if (str[pos] == '(')
			{
				if (getType(str[pos + 1]) != Qualif)
				{
					if (isQual)
					{
						nextIsQual = false;
						IsQuialNode = true;
					}
					//if(str[pos+1]!='(')
					pos++;
				}
				else {
					nextIsQual = true;
					IsQuialNode = false;
				}
				int index = conti||!isQual ? thisIndex : thisIndex + 1;
				if (index > thisIndex)
					curIndex++;
				curNode->child = createNode(str, len, pos, index, curIndex, isConti,nextIsQual);
			}
		}
		//if (isQual && str[pos] == '(' && str[pos + 1] == '(')
			//pos++;
		if (str[pos] == ')')
		{
			pos++;
			if (IsQuialNode)
			{
				curIndex--;
				//pos++;
			}
		}
		while (pos<len&&getType(str[pos]) == Linker&&curIndex==thisIndex)
		{
			curNode->broLink = str[pos];
			pos++;
			curNode->brother = createNode(str, len, pos,thisIndex,curIndex,conti);
		}
	}
	return curNode;
}

LogicNode* strToTree(char* str, int len)
{
	LogicNode* root = new LogicNode;
	root->emptyFlag = true;
	root->isLeaf = false;
	int pos = 0;
	int index = 0;
	root->child = createNode(str, len, pos,0,index,false);
	return root;
}

int formRead(wchar_t* a, char* str,bool*exisUsed)
{
	int i = 0;
	for (i = 0; a[i] != '\0'; i++)
	{
		switch (a[i]) {
		case(L'{'):
		case(L'('):
		case(L'['):
			str[i] = '(';
			break;
		case(L')'):
		case(L'}'):
		case(L']'):
			str[i] = ')';
			break;
		case(L'∃'):
			str[i] = '@';
			break;
		case(L'∀'):
			str[i] = '#';
			break;
		case(L'↔'):
			str[i] = '$';
			break;
		case(L'→'):
			str[i] = '-';
			break;
		case(L'¬'):
			str[i] = '!';
			break;
		case(L'∧'):
			str[i] = '*';
			break;
		case(L'∨'):
			str[i] = '+';
			break;
		default:
			str[i] = (char)a[i];
			if (isUpper(a[i])&&exisUsed)
				exisUsed[a[i] - 'A'] = true;
			break;
		}
	}
	return i;
}

wchar_t corre(char c)
{
	switch (c)
	{
	case('@'):
		return L'∃';
	case('#'):
		return L'∀';
	case('$'):
		return L'↔';
	case('-'):
		return L'→';
	case('!'):
		return L'¬';
	case('*'):
		return L'∧';
	case('+'):
		return L'∨';
	default:
		return (wchar_t)c;
	}
}

void showNode(LogicNode* root, char* str, int& pos)
{
	if (!root)
		return;
	if (root->quaNum > 0)//量词节点
	{
		for (int i = 0; i < root->quaNum; i++)
		{
			str[pos++] = '(';
			str[pos++] = root->qualifiers[i].type;
			str[pos++] = root->qualifiers[i].var;
			str[pos++] = ')';
		}
		str[pos++] = '(';
		showNode(root->child, str, pos);
		str[pos++] = ')';
		if (root->brother)
		{
			str[pos++] = root->broLink;
			showNode(root->brother, str, pos);
		}
		return;
	}
	if (!root->isLeaf)//非叶子节点
	{
		if (root->emptyFlag)
		{
			showNode(root->child, str, pos);
			if (root->brother)
			{
				str[pos++] = root->broLink;
				showNode(root->brother, str, pos);
			}
			return;
		}
		else
		{
			if (root->antiFlag)
				str[pos++] = '!';
			str[pos++] = '(';
			showNode(root->child, str, pos);
			str[pos++] = ')';
			if (root->brother)
			{
				str[pos++] = root->broLink;
				showNode(root->brother, str, pos);
			}
			return;
		}
	}
	//叶子节点
	if (root->emptyFlag)
		return;
	if (root->antiFlag)//输出非标志
		str[pos++] = '!';
	for (int i = 0; i < root->nameLen; i++)//输出子句名
	{
		str[pos++] = root->name[i];
	}
	if (root->varsNum > 0)//输出所有参数
	{
		str[pos++] = '(';
		int varpos = 0;
		for (int i = 0; i < root->varsNum; i++)
		{
			str[pos++] = root->vars[varpos++];
			if (root->vars[varpos] == '(')
			{
				str[pos] = root->vars[varpos];
				while (root->vars[varpos] != ')')
				{
					str[++pos] = root->vars[++varpos];
				}
				pos++;
				varpos++;
			}
			str[pos++] = ',';
		}
		pos--;//去掉多余逗号
		str[pos++] = ')';
	}
	if (root->brother)
	{
		str[pos++] = root->broLink;
		showNode(root->brother, str, pos);
	}
	return;
}

int treeToStr(LogicNode* root, char* str)
{
	int pos = 0;
	showNode(root, str, pos);
	return pos;
}

LogicNode* copyTree(LogicNode* root,bool isRoot)
{
	if (!root)
		return nullptr;
	LogicNode* nRoot = new LogicNode;
	nRoot->antiFlag = root->antiFlag;
	if(!isRoot)
		nRoot->broLink = root->broLink;
	nRoot->isLeaf = root->isLeaf;
	nRoot->emptyFlag = root->emptyFlag;
	for (int i = 0; i < TEXTLEN; i++)
	{
		nRoot->name[i] = root->name[i];
		nRoot->vars[i] = root->vars[i];
	}
	for (int i = 0; i < 10; i++)
		nRoot->qualifiers[i] = root->qualifiers[i];
	nRoot->quaNum = root->quaNum;
	nRoot->nameLen = root->nameLen;
	nRoot->varsNum = root->varsNum;
	if(!isRoot)
		nRoot->brother = copyTree(root->brother,false);
	nRoot->child = copyTree(root->child,false);
	return nRoot;
}

/*
LogicNode* copyTreeWithoutBro(LogicNode* root)
{
	if (!root)
		return nullptr;
	LogicNode* nRoot = new LogicNode;
	nRoot->antiFlag = root->antiFlag;
	nRoot->broLink = root->broLink;
	nRoot->isLeaf = root->isLeaf;
	nRoot->emptyFlag = root->emptyFlag;
	for (int i = 0; i < TEXTLEN; i++)
	{
		nRoot->name[i] = root->name[i];
		nRoot->vars[i] = root->vars[i];
	}
	for (int i = 0; i < 10; i++)
		nRoot->qualifiers[i] = root->qualifiers[i];
	nRoot->quaNum = root->quaNum;
	nRoot->nameLen = root->nameLen;
	nRoot->varsNum = root->varsNum;
	nRoot->brother = copyTree(root->brother);
	nRoot->child = copyTree(root->child);
	return nRoot;
}
*/

LogicNode* copyNode(LogicNode* root)
{
	if (!root)
		return nullptr;
	LogicNode* nRoot = new LogicNode;
	nRoot->antiFlag = root->antiFlag;
	nRoot->broLink = root->broLink;
	nRoot->isLeaf = root->isLeaf;
	for (int i = 0; i < TEXTLEN; i++)
	{
		nRoot->name[i] = root->name[i];
		nRoot->vars[i] = root->vars[i];
	}
	for (int i = 0; i < 10; i++)
		nRoot->qualifiers[i] = root->qualifiers[i];
	nRoot->quaNum = root->quaNum;
	nRoot->nameLen = root->nameLen;
	nRoot->varsNum = root->varsNum;
	nRoot->emptyFlag = root->emptyFlag;
	return nRoot;
}

void deleteTree(LogicNode* root)
{
	if (!root)
		return;
	deleteTree(root->child);
	deleteTree(root->brother);
	delete root;
}

LogicNode* collectUsefulNodes(LogicNode* root,char link)
{
	if (!root)
		return nullptr;
	LogicNode* t=nullptr, * p, * cp, * bp;
	if (root->quaNum > 0)
	{
		root->child = collectUsefulNodes(root->child,root->child->broLink);
		return root;
	}
	else if (root->isLeaf)
	{
		if (root->emptyFlag)
			return collectUsefulNodes(root->brother);
		if (root->brother)
		{
			t = new LogicNode;
			t->isLeaf = false;
			t->broLink = link;
			t->child = root;
			p = root;
			root->brother = collectUsefulNodes(root->brother);
			return t;
		}
		else
		{
			root->broLink = link;
			return root;
		}

	}
	else if (!root->isLeaf && !root->child)
	{
		return collectUsefulNodes(root->brother, link);
	}
	else if (root->brother)
	{
		cp = root->child;
		bp = root->brother;
		t=collectUsefulNodes(cp, root->broLink);
		p=collectUsefulNodes(bp, link);
		if (t)
			t->brother = p;
		else
			t = p;
		
		if (link != root->broLink)
		{
			p = new LogicNode;
			p->isLeaf = false;
			p->child = t;
			p->broLink = link;
			return p;
		}
		delete root;
		return t;
	}
	if (link)
	{
		//root->broLink = link;
		//t = root->child;
		//root->child = collectUsefulNodes(t);
		//return root;
		t = collectUsefulNodes(root->child);
		t->broLink = link;
		return t;
	}
	t = root->child;
	delete root;
	if (t->isLeaf && t->emptyFlag)
		t = t->brother;
	return collectUsefulNodes(t,link);
}



void letLeafFirst(LogicNode* root,LogicNode* parent)
{
	if (!root)
		return;
	if (root->child)
		letLeafFirst(root->child, root);
	if (!parent)
		return;
	LogicNode* curBro,*broFront;
	if (root->brother)
	{
		char c = root->broLink;
		curBro = root->brother;
		broFront = root;
		while (curBro)
		{
			if (curBro->isLeaf)
			{
				curBro->broLink = c;
				broFront->brother = curBro->brother;
				curBro->brother = parent->child;
				parent->child = curBro;
				curBro = broFront->brother;
			}
			else
			{
				broFront = curBro;
				curBro = curBro->brother;
			}
		}
		curBro = parent->child;
		while (curBro)
		{
			letLeafFirst(curBro->child, curBro);
			if (!curBro->brother)
				curBro->broLink = '\0';
			curBro = curBro->brother;
		}
	}
}

void settleTree(LogicNode* root, LogicNode* front, bool parentFlag, char depLink,char* concludeReflect)
{
	if (!root)
		return;
	if (root->child)
	{
		settleTree(root->child, root, true, root->child->broLink, concludeReflect);
	}
	LogicNode* nBro, * p, * cFront;
	nBro = root->brother;
	cFront = root;
	if (concludeReflect&&root->isLeaf)
	{
		for (int i = 0; i < TEXTLEN; i++)
			if (isLower(root->vars[i]) && concludeReflect[root->vars[i] - 'a'])
				root->vars[i] = concludeReflect[root->vars[i] - 'a'];
	}
	if (root->child && !root->child->brother)
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
		deleteTree(root->child);
		root->child = nullptr;
	}
	else if (root->child && root->child->broLink == depLink && front)
	{
		p = root->child;
		if (parentFlag)
			front->child = root->child;
		else
		{
			front->brother = root->child;
			front->broLink = depLink;
		}
		while (p->brother)
			p = p->brother;
		p->broLink = depLink;
		p->brother = nBro;
		cFront = p;
		delete root;
	}
	settleTree(nBro, cFront, false, depLink, concludeReflect);
}

void adjustTree(LogicNode*& root)
{
	if (!root||!root->child)
		return;
	LogicNode* nRoot = root;
	if (root->brother)
	{
		root = new LogicNode;
		root->child = nRoot;
		root->isLeaf = false;
		root->emptyFlag = true;
	}
	if (!root->quaNum)
		root->emptyFlag = true;
	settleTree(root, nullptr, false, '\0', nullptr);
	//showTree(root);
	letLeafFirst(root, nullptr);
	//showTree(root);
}

int showTree(LogicNode* root, bool showClause)
{
	int nLen;
	char str[1000];
	nLen = treeToStr(root, str);
	if (!nLen)
	{
		std::wcout << L"null" << std::endl;
		return nLen;
	}
	for (int i = 0; i < nLen; i++)
	{
		if (showClause && str[i] == '*')
			std::wcout << L' ';
		else
			std:: wcout << corre(str[i]);
	}
	std::wcout << std::endl;
	return nLen;
}