<?php
require 'vendor/autoload.php';

$memcached = new \Memcached();
$memcached->addServer('memcached', 11211);

$ganesha = Ackintosh\Ganesha\Builder::withCountStrategy()
    ->adapter(new Ackintosh\Ganesha\Storage\Adapter\Memcached($memcached))
    ->failureCountThreshold(3)
    ->intervalToHalfOpen(10)
    ->build();

$ganesha->reset();
