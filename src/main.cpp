/*
(1) 消蕴含和等价：利用P→Q = ¬P∨Q；P↔Q =（P∧Q）∨（¬P∧¬Q）等价关系消去蕴含符“→”和双条件符“↔”
(2)否定内移：利用¬¬P = P；¬（P∨Q）= ¬P∧¬ Q；¬（P∧Q）= ¬P∨¬ Q；¬ (∃x)P = (∀x)(¬P) ；¬(∀x)P = (∃x)(¬P)等价关系把否定符号“¬”移到紧靠谓词位置上
(3)变量标准化： 利用(∀x)P（x）= (∀y)P（y）；(∃x)P（x）= (∃y)P（y）等价关系将变量标准化，即使每个量词采用不同的变量
(4)消去存在量词∃：如果存在量词不在任何一个全称量词的辖域内，则该存在量词不依赖于任何其它的变量，因此可用一个新的个体常量代替 
如将(∃x)P（x）化为P(A)如果存在量词是在全称量词的辖域内（如在公式(“∀y)（(∃x)P（x，y））中，变量x的取值依赖于变量y的取值）
由Skolem函数（f(y)）表示依赖关系 注意，函数名应是原合式公式中没有的。
(5)将公式化为前束形：把所有全称量词移到公式的左边，并使每个量词的辖域包含这个量词后面的整个部分，所得的公式称为前束形
(6)化为合取范式:利用P∨（Q∧R）=（P∨Q）∧（P∨R）；（P∧Q）∨（P∧R）= P∧（Q∨R）等价关系将母式化为合取范式（子句的合取式）
(7)略去全称量词：母式中的变量都是全称量词量化的变量
(8)消去合取符号∧，把母式用子句集表示，如：P∧Q可表示为成子句集： P Q
(9)子句变量标准化：重新命名变量，使每个子句中的变量符号不同

(∀x){[¬P(x)∨¬Q(x)]→(∃y)[S(x,y)∧Q(x)]∧(∀x)[P(x)∨B(x)]}

(1)(∀x){¬[¬P（x）∨¬Q(x)]∨(∃ y)[S(x，y)∧Q(x)]}∧(∀x)[P（x）∨B（x）]
(2)(∀x){[P（x）∧Q(x)]∨(∃ y)[S(x，y)∧Q(x)]}∧(∀x)[P（x）∨B（x）]
(3)(∀x){[P（x）∧Q(x)]∨(∃ y)[S(x，y)∧Q(x)]}∧(∀w)[P（w）∨B（w）]
(4)(∀x)（{[P（x）∧Q(x )]∨[S(x，f (x) ) ∧Q(x )]}∧(∀ w)[ P（w）∨B（w）]）
(5)(∀x)(∀w){[P（x）∧Q(x)]∨[S(x，f(x))∧Q(x)]}∧[P（w）∨B（w）]
(6) (∀x)(∀w){[P（x）∨S(x，f(x))]∧Q(x)∧[P（w）∨B（w）]}
(7) [P（x）∨S(x，f(x))]∧Q(x)∧[P（w）∨B（w）]
(8) 子句集为： P（x）∨S(x，f(x)）；Q(x)；P（w）∨B（w）
(9) 子句变量标准化后，最终的子句集为：
P（x）∨S（x，f(x)）；Q（y）；P（w）∨B（w）

*/

/*
格式规范：
1.量词后面比跟括号表明其作用范围
2.所有不同运算之间必用括号明确其优先级
3.变量内部参数必须是单个字母且按字典序排列
4.暂时不适用于过于复杂的句子，譬如变量过多导致26个字母不够用的情况
5.如果要进行归结，全集使用单个大写字母的集合表示，且与原本使用的大写字母间不能冲突
*/

#include<iostream>
#include<io.h>
#include<fcntl.h>
#include"convertTree.h"
#include"convertClause.h"

using namespace std;
//(∀x){{[¬P(x)∨¬Q(x)]→(∃y)[S(x,y)∧Q(x)]}∧(∀x)[P(x)∨B(x)]}
//(¬(∀x)(R(x)))→(∀x)(∀y)(¬P(x,y)→¬Q(x))
//A↔B
//(P∧Q)∨(P∧R)
//p→(q→p)
//P→((P→Q)∧¬(¬Q∨¬P))
//((P∧Q)∧((P→R)∧(Q→S)))→(S∧R)
/*
∃	@
∀	#
↔	$
→	-
¬	!
∧	*
∨	+
*/
bool* exisUsed;
//(A+B)*(C+D+E)*B*C*(B+C+(A*D)+F)
//P∨(Q∧R)

void generate_clause(LogicNode*& root, char* u, int len, bool conclude = false);

void generate_clause(LogicNode*& root,char* u,int len,bool conclude)
{
	for (int i = 0; i < 26; i++)
	{
		clauseVariUsed[i] = 0;
		reflect[i] = { 0 };
	}
	first_del_arrow(root);
	wcout << L" (1) 消蕴含和等价：" << endl;
	showTree(root);
	second_del_neg(root);
	wcout << L"(2)否定内移：" << endl;
	showTree(root);
	third_var_regulation(root);
	wcout << L"(3)变量标准化：" << endl;
	showTree(root);
	char base[TEXTLEN] = { 0 };
	char exist[TEXTLEN] = { 0 };
	fourth_del_exist(root, base, 0, exist, 0,exisUsed);
	wcout << L"(4)消去存在量词：" << endl;
	showTree(root);
	fifth_mov_all(root, root);
	wcout << L"(5)将公式化为前束形：" << endl;
	showTree(root);
	root = collectUsefulNodes(root);
	//cout << "...." << endl;
	//showTree(root);
	adjustTree(root);
	wcout << L"(5.5)调整形式:" << endl;
	showTree(root);
	sixth_convert_cnf(root);
	wcout << L"(6)化为合取范式:" << endl;
	showTree(root);
	int status=mergeRoot(root,conclude);
	wcout << L"(6.5)化简：" << endl;
	if (status == isNull)
	{
		wcout << L"null" << endl;
		if (conclude)
			wcout << L"结论：命题的否定归结出空子句，原命题成立！" << endl;
		else
			wcout << L"前提归结出空子句，前提不成立！" << endl;
		return;
	}
	showTree(root);
	seventh_del_all(root);
	wcout << L"(7)略去全称量词：" << endl;
	showTree(root);
	wcout << L"(8)消去合取符号：" << endl;
	showTree(root, true);
	ninth_clause_var_regu(root,u,len);
	wcout << L"(9)子句变量标准化：" << endl;
	int t=showTree(root, true);
	if (conclude)
	{
		if (!t)
			wcout << L"结论：命题的否定归结出空子句，原命题成立！" << endl;
		else
			wcout << L"结论：命题的否定归结出非空子句，原命题不成立！" << endl;
	}
}

//(#x)(pass(x)-happy(x))*(#y)((learn(y)+lucky(y))-(pass(y)))*(!(learn(A)))*lucky(A)*(#t)(lucky(t)-win(t))
//(#x)(#y)(murder(x,y)-hate(x,y))*(#m)(hate(A,m)-!hate(C,m))*(#n)(!isB(n)-hate(A,n))*!isB(A)*!isB(C)*isB(B)*(#t)(lessWealthy(t,A)-hate(B,t))*(#s)(hate(A,s)-hate(B,s))*!(@p)(#q)(hate(p,q))*(#j)(#k)(murder(j,k)-lessWealthy(j,k))*(@e)(murder(e,A))

int main()
{
	_setmode(_fileno(stdout), _O_U16TEXT);
	_setmode(_fileno(stdin), _O_U16TEXT);
	wchar_t a[1000] = { 0 };
	char str[1000] = { 0 };
	wchar_t wu[30] = { 0 };
	char u[30] = { 0 };
	int uLen = 0;
	exisUsed=new bool[26];
	for (int i = 0; i < 26; i++)
		exisUsed[i] = 0;
	wcout << L"请输入元素全集（大写字母）:"<<endl;
	wcout << L"**注意：若输入非大写字母，则只可进行命题逻辑归结，不可进行一阶逻辑归结**" << endl;
	wcin >> wu;

	for (int i = 0; i < 30; i++)
	{
		u[i] = (char)wu[i];
		if (isUpper(u[i]))
		{
			exisUsed[u[i] - 'A'] = true;
		}
	}
	while (u[uLen])
		uLen++;
	if (!isUpper(u[0]))
		uLen = 0;
	wcout << L"请输入前提：" << endl;
	wcin >> a;
	int len= formRead(a, str);
	wcout << L">>>>>化为子句<<<<<" << endl;
	LogicNode* root=strToTree(str,len);
	generate_clause(root,u,uLen);
	wcout << L">>>>>开始归结<<<<<" << endl;
	//if (uLen)
	wcout << L"处理存在量词：" << endl;
	deal_exist(root, u, uLen);
	int ori=showTree(root);
	if (!ori)
	{
		wcout << L"前提归结为空子句，归结结束！" << endl;
		deleteTree(root);
		system("pause");
		return 0;
	}
	wchar_t b[1000] = { 0 };
	char bStr[1000] = { 0 };
	//LogicNode* concludeRoot=copyTree(root);//始终与前提归结出的root保持一致，可多次证明结论
	LogicNode* proNode, * addPos,*nRoot;//proNode是需要证明的命题所形成的节点，addPos是proNode应该添加位置的前驱
	wcout << L"请输入欲判明真假的命题：" << endl;
	for (int i = 0; i < 1000; i++)
		b[i] = 0;
	wcin >> b;
	int bLen = formRead(b, bStr, exisUsed);
	proNode = strToTree(bStr, bLen);
	if (!proNode)
		return 0;
	proNode->antiFlag = true;
	proNode->emptyFlag = false;
	addPos = root->child;
	if (!addPos || addPos->broLink == '+')
	{
		nRoot = new LogicNode;
		nRoot->child = root;
		root->broLink = '*';
		root->brother = proNode;
		root = nRoot;
	}
	else
	{
		while (addPos->brother)
			addPos = addPos->brother;
		addPos->broLink = '*';
		addPos->brother = proNode;
	}
	wcout << L"（0）将命题的否定加入前提子句集：" << endl;
	showTree(root);
	generate_clause(root, u, uLen, true);
	deleteTree(root);
	//deleteTree(concludeRoot);
	delete[]exisUsed;
	system("pause");
	return 0;
	system("pause");
	return 0;
}


/*
(  (  ((  (A*!B)  +  (!A*B)  ))  +  C  )  *  (  ((  (!A+B)  *  (A+!B)  ))  +  !C  )  )
(A↔B)↔C
*/
