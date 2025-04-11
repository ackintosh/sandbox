import json
import pandas
from sklearn.model_selection import train_test_split
import xgboost
from xgboost import DMatrix, train

def main():
    X_train = pandas.read_csv("feature_train.txt", encoding="utf-8", header=None)
    X_eval = pandas.read_csv("feature_test.txt", encoding="utf-8", header=None)
    group_train = pandas.read_csv("group_train.txt", encoding="utf-8", header=None)
    group_eval = pandas.read_csv("group_test.txt", encoding="utf-8", header=None)
    y_train = pandas.read_csv("label_train.txt", encoding="utf-8", header=None)
    y_eval = pandas.read_csv("label_test.txt", encoding="utf-8", header=None)

    # ##########################
    # モデルの学習を実行してJSONで出力する
    # ##########################
    ranker = xgboost.XGBRanker(
        objective='rank:pairwise',
        learning_rate=0.1,
        n_estimators=50,
        random_state=42,
        eval_metric='ndcg',
    )
    ranker.fit(
        X_train, y_train,
        group=group_train,
        eval_set=[(X_eval, y_eval)],
        eval_group=[group_eval],
    )

    ranker.get_booster().dump_model(
        "model.json",
        fmap="fmap.txt",
        dump_format="json",
    )

    # ########################################
    # モデルをElasticsearchにアップロードする形式に整えてファイル出力する
    # ########################################
    # 前段でファイル出力したモデルを読み込む
    with open("model.json", "r", encoding="utf-8") as f:
        model = f.read()

    # https://elasticsearch-learning-to-rank.readthedocs.io/en/latest/training-models.html#uploading-a-model
    wrapped_model = {
        "model": {
            "name": "my_model",
            "model": {
                "type": "model/xgboost+json",
                "definition": model,
            }
        }
    }

    with open("model.json", "w", encoding="utf-8") as f:
        json.dump(wrapped_model, f, indent=2)


main()
