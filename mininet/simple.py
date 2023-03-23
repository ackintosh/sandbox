from mininet.net import Mininet
from mininet.node import Controller, OVSSwitch
from mininet.cli import CLI
import time

net = Mininet(controller=Controller, switch=OVSSwitch)

c0 = net.addController('c0')

s1 = net.addSwitch('s1')

h1 = net.addHost('h1')
h2 = net.addHost('h2')

net.addLink(h1, s1)
net.addLink(h2, s1)

# ネットワークを開始
net.start()

print('========== 任意のコマンドを実行する ==========')
print(h1.cmd('echo "Hello, Mininet!"'))
print(h1.cmd('pwd'))
print(h1.cmd('ifconfig'))
print(h2.cmd('ifconfig'))

print('========== デーモンプログラムの終了を待つ ==========')
h1.cmd('nohup sleep 5 &')
h2.cmd('nohup sleep 5 &')

while h1.cmd('pidof sleep') or h2.cmd('pidof sleep'):
    print('実行中...')
    time.sleep(1)

print('デーモンプログラム終了')

# すべてのホスト間で ping コマンドを実行
net.pingAll()

# インタラクティブなCLIを提供
# CLI(net)

# ネットワークを停止
net.stop()

