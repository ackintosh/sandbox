--------------------------- MODULE SimpleProgram ---------------------------
\* see https://dev.classmethod.jp/articles/tlaplus-basic-grammer/

\* Integersモジュールの読み込み
\* Cmd + Clickでモジュールの定義に飛べる
EXTENDS Integers

\* 状態変数の宣言
\* SpecにおいてGlobalな変数として定義される
VARIABLES i, pc

\* Label
\* "Pick ==" や "Add1 ==" はLabelをつけて式をグルーピングして見やすくしたもの
\* TLA+では Init state と Next state さえ定義していれば問題ない
\* == は defines と読み替える. 代入や定義を表す
\* = は比較を表す. (ただし文脈によって例外あり)

\* Init state
\* VARIABLESで定義した変数の初期値を定義する
\* ここでの = は "現在の" 変数への代入を意味する（比較ではない）
\* /\ は "AND" に相当する
\* TLA+は基本的に論理演算の集合
\* 代入は問答無用で TRUE が返ってくるため、下記の Init 式は "TRUE AND TRUE" で最終的な評価は TRUE になる
Init == (pc = "start") /\ (i = 0)

Pick == /\ pc = "start"
/\ i' \in 1..1000
/\ pc' = "middle"

Add1 == /\ pc = "middle"
/\ i' = i + 1
/\ pc' = "done"

\* Next state
\* Next Stateでは、変数の取りうるすべての値域と状態遷移を式で表記し、取りうる変数の組み合わせの集合を定義する
\* \/ は "OR" に相当する
\* 下記では Pick と Add1 の式を評価してその結果を OR でつなぐ
\* OR でそれぞれの状態を表す式をつなぐことで、全ての取りうる状態の集合を表現できる
Next == \/ Pick \/ Add1

=============================================================================
\* Modification History
\* Last modified Mon Jun 28 08:33:28 JST 2021 by abi01357
\* Created Mon Jun 28 08:01:41 JST 2021 by abi01357
