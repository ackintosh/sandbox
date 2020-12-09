<?php
namespace Ackintosh;

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

        $conn = pg_connect("host=localhost port=5432 user=sandbox_user password=sandbox_password");
        var_dump($conn);
        self::assertSame("", "");
    }
}
