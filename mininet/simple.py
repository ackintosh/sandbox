from mininet.net import Mininet
from mininet.node import Controller, OVSSwitch
from mininet.cli import CLI

net = Mininet(controller=Controller, switch=OVSSwitch)

c0 = net.addController('c0')

s1 = net.addSwitch('s1')

h1 = net.addHost('h1')
h2 = net.addHost('h2')

net.addLink(h1, s1)
net.addLink(h2, s1)

# ネットワークを開始
net.start()

# 任意のコマンドを実行する
print(h1.cmd('echo "Hello, Mininet!"'))
print(h1.cmd('pwd'))
print(h1.cmd('ifconfig'))
print(h2.cmd('ifconfig'))

# すべてのホスト間で ping コマンドを実行
net.pingAll()

# インタラクティブなCLIを提供
# CLI(net)

# ネットワークを停止
net.stop()

