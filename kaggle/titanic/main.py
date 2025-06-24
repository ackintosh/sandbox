from sklearn.preprocessing import LabelEncoder
import pandas as pd
import numpy as np

# -----------------------------------
# 学習データ、テストデータの読み込み
# -----------------------------------
# 学習データ、テストデータの読み込み
train = pd.read_csv('./data/train.csv')
test = pd.read_csv('./data/test.csv')

# 学習データを特徴量と目的変数に分割
train_x = train.drop(['Survived'], axis=1)
train_y = train['Survived']

# テストデータは特徴量のみなので、目的変数は不要
test_x = test.copy()

# #############################################
# 特徴量の作成
# #############################################
# *** 変数PassengerIdは不要なので削除 ***
# PassengerIdは予測に寄与する変数ではなく、入れたままだとモデルが意味のある変数と勘違いしてしまう恐れがあるため
# その変数の列を削除する
train_x = train_x.drop(['PassengerId'], axis=1)
test_x = test_x.drop(['PassengerId'], axis=1)

# *** 変数Name, Ticket, Cabinは不要なので削除 ***
# 上手く使えば予測に有用そうだが、やや煩雑な処理が必要そうなので
# 一旦これらの変数の列を削除する
train_x = train_x.drop(['Name', 'Ticket', 'Cabin'], axis=1)
test_x = test_x.drop(['Name', 'Ticket', 'Cabin'], axis=1)

# *** それぞれのカテゴリ変数にlabel encodingを適用 ***
# GBDTでは、文字列をそのまま入れてもエラーとなってしまうため、何らかの方法で数値に変換する必要がある
# ここでは label encoding という方法を使う
# 欠損については、GBDTではそのまま扱うことができるため、特に処理を行う必要はない(欠損を補完するのも1つの方法)
for c in ['Sex', 'Embarked']:
    # 学習データに基づいてどう変換するのか定める
    le = LabelEncoder()
    le.fit(train_x[c].fillna('NA'))

    # 学習データ、テストデータの両方に変換を適用
    train_x[c] = le.transform(train_x[c].fillna('NA'))
    test_x[c] = le.transform(test_x[c].fillna('NA'))

# #############################################
# モデル作成
# #############################################
from xgboost import XGBClassifier
# モデルの作成および学習データを与えての学習
model = XGBClassifier(
    n_estimators=20,  # 木の数
    random_state=71,  # 乱数シード
)
model.fit(train_x, train_y)

# テストデータに対する予測を確率で出力する
pred = model.predict_proba(test_x)[:, 1]

# テストデータに対する予測を二値で出力する
pred_label = np.where(pred > 0.5, 1, 0)

# 提出用ファイルの作成
submission = pd.DataFrame({
    'PassengerId': test['PassengerId'],
    'Survived': pred_label
})
submission.to_csv('./data/submission.csv', index=False)

# #############################################
# クロスバリデーションによりモデルを評価する
# #############################################

# 各foldのスコアを保存するリスト
from sklearn.model_selection import KFold
from sklearn.metrics import log_loss, accuracy_score
scores_accuracy = []
scores_logloss = []

# *** クロスバリデーションを行う ***
# 学習データを4分割し 1つをバリデーションデータとすることを、バリデーションデータを変えて繰り返す
kf = KFold(n_splits=4, shuffle=True, random_state=71)
# ループのたびにモデルを作り直すことで、各foldで独立した評価が可能
# これにより特徴量の妥当性やモデルの汎化性能を正確に測定できる
# 前のfoldの学習結果に影響されない「初めて見るデータ」としての評価が実現される
for tr_idx, va_idx in kf.split(train_x):
    # 学習データを、学習データとバリデーションデータに分割
    tr_x, va_x = train_x.iloc[tr_idx], train_x.iloc[va_idx]
    tr_y, va_y = train_y.iloc[tr_idx], train_y.iloc[va_idx]

    # モデルの学習を行う
    model = XGBClassifier(
        n_estimators=20,  # 木の数
        random_state=71,  # 乱数シード
    )
    model.fit(tr_x, tr_y)

    # バリデーションデータの予測を確率で出力する
    va_pred = model.predict_proba(va_x)[:, 1]
    # バリデーションデータでのスコアを計算する
    logloss = log_loss(va_y, va_pred)
    accuracy = accuracy_score(va_y, va_pred > 0.5)
    # そのfoldのスコアを保存する
    scores_logloss.append(logloss)
    scores_accuracy.append(accuracy)

# 各foldのスコアの平均を出力する
logloss = np.mean(scores_logloss)
accuracy = np.mean(scores_accuracy)
print(f'logloss: {logloss:.4f}, accuracy: {accuracy:.4f}')

# ############################################
# モデルチューニング
# ############################################
import itertools

# チューニング対象のパラメータを準備する
param_space = {
    'max_depth': [3, 5, 7],  # 木の深さ
    'min_child_weight': [1.0, 2.0, 4.0],  # 葉の最小重み
}

# 探索するハイパーパラメータの組み合わせ
param_conbinations = itertools.product(*param_space.values())

# 各パラメータの組み合わせ、それに対するスコアを保存するリスト
params = []
scores = []

# 各パラメータの組み合わせごとに、クロスバリデーションで評価する
for max_depth, min_child_weight in param_conbinations:
    score_folds = []
    # クロスバリデーションを行う
    # 学習データを4分割し 1つをバリデーションデータとすることを、バリデーションデータを変えて繰り返す
    kf = KFold(n_splits=4, shuffle=True, random_state=12345)
    for tr_idx, va_idx in kf.split(train_x):
        # 学習データを、学習データとバリデーションデータに分割
        tr_x, va_x = train_x.iloc[tr_idx], train_x.iloc[va_idx]
        tr_y, va_y = train_y.iloc[tr_idx], train_y.iloc[va_idx]

        # モデルの学習を行う
        model = XGBClassifier(
            n_estimators=20,  # 木の数
            random_state=71,  # 乱数シード
            max_depth=max_depth,  # 木の深さ
            min_child_weight=min_child_weight,  # 葉の最小重み
        )
        model.fit(tr_x, tr_y)

        # バリデーションデータの予測を確率で出力する
        va_pred = model.predict_proba(va_x)[:, 1]
        # バリデーションデータでのスコアを計算する
        logloss = log_loss(va_y, va_pred)
        score_folds.append(logloss)

    # 各foldのスコアの平均を計算する
    score_mean = np.mean(score_folds)
    # パラメータとスコアを保存する
    params.append((max_depth, min_child_weight))
    scores.append(score_mean)

# 最もスコアが良いものをベストなパラメータとする
best_idx = np.argmin(scores)
print('scores', scores)
print('best_idx', best_idx)
best_param = params[best_idx]
print(f'Best parameters: max_depth={best_param[0]}, min_child_weight={best_param[1]}')
print(f'Best logloss: {scores[best_idx]:.4f}')