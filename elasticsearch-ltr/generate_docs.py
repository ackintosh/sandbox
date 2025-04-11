from faker import Faker
import json
import random

# usage:
# $ uv run generate_docs.py > docs.json

fake = Faker()

for i in range(1, 5001):
    action = {"index": {"_id": i}}
    doc = {
        "title": fake.catch_phrase(),
        "popularity": random.randint(1, 100),
    }
    print(json.dumps(action, ensure_ascii=False))
    print(json.dumps(doc, ensure_ascii=False))
