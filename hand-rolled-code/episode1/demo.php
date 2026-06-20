<?php
require 'vendor/autoload.php';

$redis = new Redis();
$redis->connect('redis');

$ganesha = Ackintosh\Ganesha\Builder::withCountStrategy()
    ->adapter(new Ackintosh\Ganesha\Storage\Adapter\Redis($redis))
    ->failureCountThreshold(3)
    ->intervalToHalfOpen(10)
    ->build();

$service = 'payment-api';

if (!$ganesha->isAvailable($service)) {
    // fail fast - don't even try the request.
    throw new RuntimeException('Payment API is not available');
}

// try {
//     // make the actual request
//     $result = callPaymentApi();
//     $ganesha->success($service);
// } catch (RuntimeException $e) {
//     $ganesha->failure($service);
//     throw $e;
// }

$ganesha->subscribe(function (string $event, stirng $service, string $message): void {
    switch ($event) {
        case \Ackintosh\Ganesha::EVENT_TRIPPED:
            echo(sprintf('[ERROR] the circuit just opened %s(%s): %s', $event, $service, $message));
        case \Ackintosh\Ganesha::EVENT_CALMED_DOWN:
            echo(sprintf('[INFO] the circuit recovered and closed again %s(%s): %s', $event, $service, $message));
        case \Ackintosh\Ganesha::EVENT_STORAGE_ERROR:
            echo(sprintf('[WARN] the storage backend had a problem %s(%s): %s', $event, $service, $message));
        default:
            break;
    }
});

var_dump($ganesha->isAvailable($service));

$ganesha->failure($service);
$ganesha->failure($service);
$ganesha->failure($service);

var_dump($ganesha->isAvailable($service));

