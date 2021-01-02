#include <iostream>
#include <unistd.h>
#include <ctime>
#include <cmath>
#include "Point.h"
#include "Judge.h"
#include "Strategy.h"//包含判断胜负的函数userWin，machineWin和isTie

#define EMPTY 0 //未落子 
#define PLAYER_CHANCE 1 //玩家棋权 
#define COMPUTER_CHANCE 2 //电脑（AI）棋权 
#define TIME_LIMITATION 3000 //计算时长限制
#define PLAYER_WIN_PROFIT -1 //玩家获胜时的收益 
#define COMPUTER_WIN_PROFIT 1 //我方AI获胜时的收益 
#define TIE_PROFIT 0 //平局收益
#define UNTERMINAL_STATE 2 //非终止状态 
#define VITALITY_COEFFICIENT 0.8 //比例系数c 

using namespace std;

class UCT;

class Node
{
private: 
	int **boardState; //棋局状态
	int *topState; //顶端状态
	int row, column; //棋盘大小（M, N）
	int _noX, _noY; //不可落子点位置 
	int _chessman; //我方持子属性 
	int _x, _y; //前一上落子位置
	int visitedNum; //被访问次数 
	double profit; //当前状态我方收益
	int _depth; //节点深度 
	Node *father; //父节点
	Node **children; //子节点
	int expandableNum; //可扩展节点数量 
	int *expandableNode; //可扩展节点编号 
	friend class UCT;
	
	int *TopState() const { //复制棋盘顶端状态数组topState 
		int *presentTop = new int[column];
		for (int i = 0; i != column; i ++)
			presentTop[i] = topState[i];
		return presentTop;
	}
	int **BoardState() const { //复制棋盘状态数组boardState 
		int **presentBoardState = new int*[row];
		for (int i = 0; i < row; i ++) {
			presentBoardState[i] = new int[column];
			for(int j = 0; j < column; j ++)
				presentBoardState[i][j] = boardState[i][j];
		}
		return presentBoardState;
	}
	void clear() { //空间释放
		for (int i = 0; i != row; i ++)
			delete [] boardState[i];
		delete [] boardState;
		delete [] topState;
		delete [] expandableNode;
		for (int i = 0; i != column; i ++)
			if (children[i]) {
				children[i] -> clear();
				delete children[i];
			}
		delete [] children;
	}
	
public:
	//构造函数 
	Node(int **board, int *top, int r, int c, int noX, int noY, int depth = 0, int x = -1, int y = -1, int playingRight = COMPUTER_CHANCE, Node* _father = NULL): 
		boardState(board), topState(top), row(r), column(c), _noX(noX), _noY(noY), _depth(depth), _x(x), _y(y), _chessman(playingRight), visitedNum(0), profit(0), father(_father) {
		expandableNum = 0; 
		children = new Node*[column]; //大小等于行数的子节点数组 
		expandableNode = new int[column]; //可到达子节点编号的数组 
		for (int i = 0; i != column; i ++) {
			if (topState[i] != 0) //若第i列可落子 
				expandableNode[expandableNum ++] = i;
			children[i] = NULL;
		}
	}
	int x() const { return _x; }
	int y() const { return _y; }
	int chessman() const { return _chessman; }
	bool isExpandable() const { return expandableNum > 0; }//是否可扩展
	//是否为终止节点 
	bool isTerminal() {
		if (_x == -1 && _y == -1) //若为根节点 
			return false;
		if ((_chessman == PLAYER_CHANCE && machineWin(_x, _y, row, column, boardState)) || //计算机胜利 
			(_chessman == COMPUTER_CHANCE && userWin(_x, _y, row, column, boardState)) || //玩家胜利 
			(isTie(column, topState))) //平局 
			return true;
		return false;
	}
	//扩展节点 
	Node *expand(int playingRight) { 
		int index = rand() % expandableNum; //随机确定一个索引值 
		int **newBoardState = BoardState(); //复制棋盘状态数组 
		int *newTopState = TopState(); //复制棋盘顶端状态数组 
		int newY = expandableNode[index], newX = -- newTopState[newY]; //确定落子坐标 
		newBoardState[newX][newY] = chessman(); //落子 
		if (newX - 1 == _noX && newY == _noY) //若落子位置的正上方位置是不可落子点 
			newTopState[newY] --; //更新棋盘顶端状态数组
		//为当前节点创建扩展子节点 
		children[newY] = new Node(newBoardState, newTopState, row, column, _noX, _noY, _depth + 1, newX, newY, playingRight, this);
		swap(expandableNode[index], expandableNode[-- expandableNum]); //将被选中子节点编号置换到目录末尾
		return children[newY];
	}
	//最优子节点
	Node *bestChild() {
		Node* best;
		double maxProfitRatio = -RAND_MAX;
		for (int i = 0; i != column; i ++) {
			if (children[i] == NULL) continue;
			double modifiedProfit = (player == PLAYER_CHANCE ? -1 : 1) * children[i] -> profit; //修正收益值
			int childVisitedNum = children[i] -> visitedNum; //子节点访问数 
			double tempProfitRatio = modifiedProfit / childVisitedNum + 
				sqrtl(2 * logl(visitedNum) / childVisitedNum) * VITALITY_COEFFICIENT; //计算综合收益率 
			if (tempProfitRatio > maxProfitRatio || (tempProfitRatio == maxProfitRatio && rand() % 2 == 0)) { //选择综合收益率最大的子节点 
				maxProfitRatio = tempProfitRatio;
				best = children[i];
			}
		}
		return best;
	} 
	//回溯更新
	void backup(double deltaProfit) {
		Node *temp = this;
		while (temp) {
			temp -> visitedNum ++; //访问次数+1 
			temp -> profit += deltaProfit; //收益增加delta 
			temp = temp -> father;
		}
	} 
};

class UCT
{
private:
	Node *_root; //根节点
	int _row, _column; //行数、列数
	int _noX, _noY; //不可落子点的位置 
	int startTime; //计算开始时间
	
	//计算当前状态收益
	int Profit(int **board, int *top, int chessman, int x, int y) const { 
		if (chessman == PLAYER_CHANCE && userWin(x, y, _row, _column, board))
			return PLAYER_WIN_PROFIT;
		if (chessman == COMPUTER_CHANCE && machineWin(x, y, _row, _column, board))
			return COMPUTER_WIN_PROFIT;
		if (isTie(_column, top))
			return TIE_PROFIT;
		return UNTERMINAL_STATE; //未进入终止状态 
	}
	//随机落子 
	void placeChessman(int **board, int *top, int chessman, int &x, int &y) {
		y = rand() % _column; //随机选择一列 
		while (top[y] == 0) //若此列已下满 
			y = rand() % _column; //再随机选择一列 
		x = -- top[y]; //确定落子高度 
		board[x][y] = chessman; //落子 
		if (x - 1 == _noX && y == _noY) //若落子位置正上方紧邻不可落子点 
			top[y] --;
	}
	//棋权变换 
	int rightChange(int chessman) const {
		if (chessman == PLAYER_CHANCE)
			return COMPUTER_CHANCE;
		else if (chessman == COMPUTER_CHANCE)
			return PLAYER_CHANCE;
		else
			return -1;
	} 
	
	//搜索树策略 
	Node *TreePolicy(Node *presentNode) {
		while (!presentNode -> isTerminal()) { //节点不是终止节点 
			if (presentNode -> isExpandable()) //且拥有未被访问的子状态 
				return Expand(presentNode); //扩展该节点 
			else
				presentNode = BestChild(presentNode); //选择最优子节点 
		}
		return presentNode;
	}
	//对节点进行扩展
	Node *Expand(Node *presentNode) { return presentNode -> expand(rightChange(presentNode -> chessman())); }
	//最优子节点 
	Node *BestChild(Node *father) { return father -> bestChild(); }
	//模拟策略 
	double DefaultPolicy(Node *selectedNode) { 
		int **boardState = selectedNode -> BoardState(), *top = selectedNode -> TopState();
		int chessman = selectedNode -> chessman(), depth = selectedNode -> _depth;
		int x = selectedNode -> x(), y = selectedNode -> y();
		int profit = Profit(boardState, top, rightChange(chessman), x, y); //计算收益 
		while (profit == UNTERMINAL_STATE) { //若当前状态未达终止状态 
			depth ++;
			placeChessman(boardState, top, chessman, x, y); //随机落子 
			profit = Profit(boardState, top, chessman, x, y); //计算收益 
			chessman = rightChange(chessman); //棋权变换 
		}
		for (int i = 0; i != _row; i ++)
			delete [] boardState[i];
		delete [] boardState;
		delete [] top;
		return double(profit);// / logl(depth + 1); //非线性加速
	}
	//回溯更新收益(深度越深收益越小)
	void Backup(Node *selectedNode, double deltaProfit) { selectedNode -> backup(deltaProfit); }
	
public:
	//构造函数 
	UCT(int row, int column, int noX, int noY): _row(row), _column(column), _noX(noX), _noY(noY), startTime(clock()) {}
	//信心上限树搜索 
	Node *UCTSearch(int **boardState, int *topState) {
		_root = new Node (boardState, topState, _row, _column, _noX, _noY); //以当前状态创建根节点 
		while (clock() - startTime <= TIME_LIMITATION) { //尚未耗尽计算时长 
			Node *selectedNode = TreePolicy(_root); //运用搜索树策略节点 
			double deltaProfit = DefaultPolicy(selectedNode); //运用模拟策略对选中节点进行一次随机模拟 
			Backup(selectedNode, deltaProfit); //将模拟结果回溯反馈给各祖先 
		}
		return BestChild(_root);
	}
	//析构函数 
	~UCT() { _root -> clear(); delete _root; } 
};

/*
	策略函数接口,该函数被对抗平台调用,每次传入当前状态,要求输出你的落子点,该落子点必须是一个符合游戏规则的落子点,不然对抗平台会直接认为你的程序有误
	
	input:
		为了防止对对抗平台维护的数据造成更改，所有传入的参数均为const属性
		M, N : 棋盘大小 M - 行数 N - 列数 均从0开始计， 左上角为坐标原点，行用x标记，列用y标记
		top : 当前棋盘每一列列顶的实际位置. e.g. 第i列为空,则_top[i] == M, 第i列已满,则_top[i] == 0
		_board : 棋盘的一维数组表示, 为了方便使用，在该函数刚开始处，我们已经将其转化为了二维数组board
				你只需直接使用board即可，左上角为坐标原点，数组从[0][0]开始计(不是[1][1])
				board[x][y]表示第x行、第y列的点(从0开始计)
				board[x][y] == 0/1/2 分别对应(x,y)处 无落子/有用户的子/有程序的子,不可落子点处的值也为0
		lastX, lastY : 对方上一次落子的位置, 你可能不需要该参数，也可能需要的不仅仅是对方一步的
				落子位置，这时你可以在自己的程序中记录对方连续多步的落子位置，这完全取决于你自己的策略
		noX, noY : 棋盘上的不可落子点(注:涫嫡饫锔?龅膖op已经替你处理了不可落子点，也就是说如果某一步
				所落的子的上面恰是不可落子点，那么UI工程中的代码就已经将该列的top值又进行了一次减一操作，
				所以在你的代码中也可以根本不使用noX和noY这两个参数，完全认为top数组就是当前每列的顶部即可,
				当然如果你想使用lastX,lastY参数，有可能就要同时考虑noX和noY了)
		以上参数实际上包含了当前状态(M N _top _board)以及历史信息(lastX lastY),你要做的就是在这些信息下给出尽可能明智的落子点
	output:
		你的落子点Point
*/
extern "C" Point* getPoint(const int M, const int N, const int* top, const int* _board, 
	const int lastX, const int lastY, const int noX, const int noY){
	/*
		不要更改这段代码
	*/
	int x = -1, y = -1;//最终将你的落子点存到x,y中
	int** board = new int*[M];
	for(int i = 0; i < M; i++){
		board[i] = new int[N];
		for(int j = 0; j < N; j++){
			board[i][j] = _board[i * N + j];
		}
	}
	
	/*
		根据你自己的策略来返回落子点,也就是根据你的策略完成对x,y的赋值
		该部分对参数使用没有限制，为了方便实现，你可以定义自己新的类、.h文件、.cpp文件
	*/
	//Add your own code below
    /*
     //a naive example
	for (int i = N-1; i >= 0; i--) {
		if (top[i] > 0) {
			x = top[i] - 1;
			y = i;
			break;
		}
	}
    */
	UCT *uct = new UCT(m, n, noX, noY);
	Node *ans->UCTSearch(board, top);
	x = ans->x();
	y = ans->y();

	/*
		不要更改这段代码
	*/
	clearArray(M, N, board);
	return new Point(x, y);
}


/*
	getPoint函数返回的Point指针是在本dll模块中声明的，为避免产生堆错误，应在外部调用本dll中的
	函数来释放空间，而不应该在外部直接delete
*/
extern "C" void clearPoint(Point* p){
	delete p;
	return;
}

/*
	清除top和board数组
*/
void clearArray(int M, int N, int** board){
	for(int i = 0; i < M; i++){
		delete[] board[i];
	}
	delete[] board;
}


/*
	添加你自己的辅助函数，你可以声明自己的类、函数，添加新的.h .cpp文件来辅助实现你的想法
*/



