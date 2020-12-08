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
        $redis->connect("redis", "6379");
        $redis->set("foo", "bar");
        self::assertSame("bar", $redis->get("foo"));
    }
}
