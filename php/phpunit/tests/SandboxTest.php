<?php
namespace Ackintosh;

use Aws\DynamoDb\Marshaler;
use Aws\Sdk;
use PHPUnit\Framework\TestCase;

class SandboxTest extends TestCase
{
    /**
     * @test
     */
    public function square(): void
    {
        $sandbox = new Sandbox();
        self::assertSame(4, $sandbox->square(2));
    }

    /**
     * @test
     */
    public function memcached(): void
    {
        if (!extension_loaded('memcached')) {
            self::markTestSkipped('No ext-memcached present');
        }

        $memcached = new \Memcached();
        $memcached->addServer('localhost', 11211);
        $memcached->set('sandbox_key', 'sandbox_value');
        self::assertSame('sandbox_value', $memcached->get('sandbox_key'));
    }

    /**
     * @test
     */
    public function redis(): void
    {
        if (!\extension_loaded('redis')) {
            self::markTestSkipped('No ext-redis present');
        }

        $redis = new \Redis();
        $redis->connect("localhost", "6379");
        $redis->set("foo", "bar");
        self::assertSame("bar", $redis->get("foo"));
    }

    /**
     * @test
     */
    public function postgresql(): void
    {
        if (!\extension_loaded('pgsql')) {
            self::markTestSkipped('No ext-pgsql present');
        }

        $conn = pg_connect("host=localhost port=5432 user=sandbox_user password=sandbox_password dbname=sandbox_db");
        var_dump(pg_dbname($conn), pg_connection_status($conn));
        self::assertSame("sandbox_db", pg_dbname($conn));
        self::assertSame(PGSQL_CONNECTION_OK, pg_connection_status($conn));
    }

    /**
     * @test
     */
    public function postgresqlSelect(): void
    {
        // GitHub Actionsでpsqldefを使って作っている sample テーブルにアクセスしているので
        // CI以外ではスキップする
        // see https://docs.github.com/ja/free-pro-team@latest/actions/reference/environment-variables
        if (getenv('CI') !== 'true') {
            self::markTestSkipped('this test case runs only in CI environment');
        }

        // GitHub Actionsでpsqldefを使って作っているテーブル
        $table_name = 'sample';

        $conn = pg_connect("host=localhost port=5432 user=sandbox_user password=sandbox_password dbname=sandbox_db");

        $res = pg_insert($conn, $table_name, ['id' => 'test_id', 'label' => 'test_label']);
        self::assertNotFalse($res);

        $res = pg_select($conn, $table_name, ['id' => 'test_id']);
        var_dump($res);
        self::assertCount(1, $res);
        self::assertSame(['id' => 'test_id', 'label' => 'test_label'], $res[0]);
    }

    /**
     * @test
     */
    public function dynamoDb(): void
    {
        // https://docs.aws.amazon.com/ja_jp/amazondynamodb/latest/developerguide/GettingStarted.PHP.01.html
        $sdk = new Sdk([
            'endpoint'   => 'http://localhost:8000',
            'region'   => 'ap-northeast-1',
            'version'  => 'latest'
        ]);
        $dynamoDb = $sdk->createDynamoDb();
        $result = $dynamoDb->createTable([
            'TableName' => 'AnotherMovies',
            'KeySchema' => [
                [
                    'AttributeName' => 'year',
                    'KeyType' => 'HASH'  //Partition key
                ],
                [
                    'AttributeName' => 'title',
                    'KeyType' => 'RANGE'  //Sort key
                ]
            ],
            'AttributeDefinitions' => [
                [
                    'AttributeName' => 'year',
                    'AttributeType' => 'N'
                ],
                [
                    'AttributeName' => 'title',
                    'AttributeType' => 'S'
                ],

            ],
            // 必須だが、dynamodb-localでは無視される
            'ProvisionedThroughput' => [
                'ReadCapacityUnits' => 10,
                'WriteCapacityUnits' => 10
            ]
        ]);

        self::assertSame(
            'ACTIVE',
            $result['TableDescription']['TableStatus']
        );
    }

    /**
     * @test
     */
    public function dynamoDbPutItem(): void
    {
        // GitHub Actionsで作っている Movies テーブルにアクセスしているので
        // CI以外ではスキップする
        // see https://docs.github.com/ja/free-pro-team@latest/actions/reference/environment-variables
        if (getenv('CI') !== 'true') {
            self::markTestSkipped('this test case runs only in CI environment');
        }

        // https://docs.aws.amazon.com/ja_jp/amazondynamodb/latest/developerguide/GettingStarted.PHP.03.html
        $sdk = new Sdk([
            'endpoint'   => 'http://localhost:8000',
            'region'   => 'ap-northeast-1',
            'version'  => 'latest'
        ]);
        $dynamoDb = $sdk->createDynamoDb();
        $marshaler = new Marshaler();

        // GitHub Actionsで作っているテーブル
        $tableName = 'Movies';

        $year = 2015;
        $title = 'The Big New Movie';

        ///////////////////////////////////////////
        // 追加
        ///////////////////////////////////////////
        $item = $marshaler->marshalJson('
    {
        "year": ' . $year . ',
        "title": "' . $title . '",
        "info": {
            "plot": "Nothing happens at all.",
            "rating": 0
        }
    }
');

        $params = [
            'TableName' => $tableName,
            'Item' => $item
        ];
        $dynamoDb->putItem($params);

        ///////////////////////////////////////////
        // 取得
        ///////////////////////////////////////////
        $key = $marshaler->marshalJson('
    {
        "year": ' . $year . ', 
        "title": "' . $title . '"
    }
');
        $params = [
            'TableName' => $tableName,
            'Key' => $key
        ];
        $result = $dynamoDb->getItem($params);
        self::assertSame($title, $result['Item']['title']['S']);
    }
}
