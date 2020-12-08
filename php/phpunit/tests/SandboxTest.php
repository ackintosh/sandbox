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
}
