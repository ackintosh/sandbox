from sklearn.datasets import load_iris
from sklearn.model_selection import train_test_split
import pandas as pd
import matplotlib.pyplot as plt
import mglearn

# ######################################################################################################################
# 1.7 最初のアプリケーション:アイリスのクラス分類
# ######################################################################################################################
def main():
    # ##################################################################################################################
    # 1.7.1 データを読む
    # ##################################################################################################################
    iris_dataset = load_iris()
    print("Keys of iris_dataset: \n{}".format(iris_dataset.keys()))
    # dict_keys(['data', 'target', 'frame', 'target_names', 'DESCR', 'feature_names', 'filename', 'data_module'])

    # キー DESCRの値は、データセットの簡単な説明(description)
    print(iris_dataset['DESCR'][:193] + "\n...")

    # キー target_namesの値は、予測しようとしている花の種類を文字列の配列として持っている
    print("Target names: {}".format(iris_dataset['target_names']))
    # ['setosa' 'versicolor' 'virginica']

    # キー feature_namesの値は、特徴量の説明を文字列のリストとして持っている
    print("Feature names: \n{}".format(iris_dataset['feature_names']))
    # ['sepal length (cm)', 'sepal width (cm)', 'petal length (cm)', 'petal width (cm)']

    # 花弁の長さ、花弁の幅が NumPy 配列として格納されている。
    print("Type of data: {}".format(type(iris_dataset['data'])))
    # Type of data: <class 'numpy.ndarray'>

    # 配列 data の行は個々の花に対応し、列は個々の花に対して行われた 4 つの測定に対応する
    print("Shape of data: {}".format(iris_dataset['data'].shape))
    # Shape of data: (150, 4)

    # 最初の5つのサンプル
    print("First five columns of data:\n{}".format(iris_dataset['data'][:5]))
    # First five columns of data:
    # [[5.1 3.5 1.4 0.2]
    #  [4.9 3.  1.4 0.2]
    #  [4.7 3.2 1.3 0.2]
    #  [4.6 3.1 1.5 0.2]
    #  [5.  3.6 1.4 0.2]]

    # 配列 target には、測定された個々の花の種類が、やはり NumPy 配列として格納されている
    print("Type of target: {}".format(type(iris_dataset['target'])))
    # Type of target: <class 'numpy.ndarray'>

    # target は 1 次元の配列で、個々の花に 1 つのエントリが対応する
    print("Shape of target: {}".format(iris_dataset['target'].shape))
    # Shape of target: (150,)

    # ターゲットの種類は 0 から 2 までの整数で、それぞれの整数が花の種類を表す
    print("Target:\n{}".format(iris_dataset['target']))
    # Target:
    # [0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
    #  0 0 0 0 0 0 0 0 0 0 0 0 0 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1
    #  1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 2 2 2 2 2 2 2 2 2 2 2
    #  2 2 2 2 2 2 2 2 2 2 2 2 2 2 2 2 2 2 2 2 2 2 2 2 2 2 2 2 2 2 2 2 2 2 2 2 2
    #  2 2]

    # ##################################################################################################################
    # 1.7.2 成功度合いの測定:訓練データとテストデータ
    # ##################################################################################################################
    # データを訓練データとテストデータに分割する
    X_train, X_test, y_train, y_test = train_test_split(
        iris_dataset['data'],
        iris_dataset['target'],
        # 同じ関数を何度か呼び出した際に、確実に同じ結果が得られるよう、random_state パラメータを 用いて擬似乱数生成器に同じシードを渡している
        random_state=0,
    )

    # 関数train_test_splitの出力はX_train、X_test、y_train、y_testとなる
    # これらはすべて NumPy 配列で、X_train にはデータセットの 75% の行が、X_test には残りの 25% の行が含まれる
    # *** 訓練データ
    print("X_train shape: {}".format(X_train.shape))
    print("y_train shape: {}".format(y_train.shape))
    # X_train shape: (112, 4)
    # y_train shape: (112,)
    # *** テストデータ
    print("X_test shape: {}".format(X_test.shape))
    print("y_test shape: {}".format(y_test.shape))
    # X_test shape: (38, 4)
    # y_test shape: (38,)

    # ##################################################################################################################
    # 1.7.3 最初にすべきこと:データをよく観察する
    # ##################################################################################################################
    # X_trainのデータからDataFrameを作る、
    # iris_dataset.feature_namesの文字列を使ってカラムに名前を付ける。
    iris_dataframe = pd.DataFrame(X_train, columns=iris_dataset.feature_names)
    # データフレームからscatter matrixを作成し、y_trainに従って色を付ける。
    grr = pd.scatter_matrix(iris_dataframe, c=y_train, figsize=(15, 15), marker='o',
                              hist_kwds={'bins': 20}, s=60, alpha=.8, cmap=mglearn.cm3)
    print("aaa")

if __name__ == "__main__":
    main()
