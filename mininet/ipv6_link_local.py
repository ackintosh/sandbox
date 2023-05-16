from mininet.net import Mininet
from mininet.node import Controller, OVSKernelSwitch
from mininet.cli import CLI
from mininet.util import dumpNodeConnections

# * Ping
# h1 ping6 -I h1-eth0 fe80::2
# h1 ping6 fe80::2

# * IPv6のルーティングテーブルを確認する
# h1 ip -6 route show

def ipv6Net():
    net = Mininet(controller=Controller, switch=OVSKernelSwitch, build=False)

    c0 = net.addController('c0')

    s1 = net.addSwitch('s1')

    h1 = net.addHost('h1')
    h2 = net.addHost('h2')

    net.addLink(h1, s1)
    net.addLink(h2, s1)

    net.build()

    # ネットワークを開始
    net.start()

    h1.cmd('ip -6 addr add fe80::1/64 dev h1-eth0')
    h2.cmd('ip -6 addr add fe80::2/64 dev h2-eth0')

    CLI(net)

    net.stop()

def ipv6NetLinkLocalScopeMultiZone():
    net = Mininet(controller=Controller, switch=OVSKernelSwitch, build=False)

    c0 = net.addController('c0')

    s1 = net.addSwitch('s1')
    s2 = net.addSwitch('s2')

    h1 = net.addHost('h1')
    h2 = net.addHost('h2')
    h3 = net.addHost('h3')

    net.addLink(h1, s1)
    net.addLink(h2, s1)

    net.addLink(h1, s2)
    net.addLink(h3, s2)

    net.build()

    # ネットワークを開始
    net.start()
    dumpNodeConnections(net.hosts)

    h1.cmd('ip -6 addr add fe80::1/64 dev h1-eth0')
    h1.cmd('ip -6 addr add fe80::1/64 dev h1-eth1')
    h2.cmd('ip -6 addr add fe80::2/64 dev h2-eth0')
    h3.cmd('ip -6 addr add fe80::2/64 dev h3-eth0')

    CLI(net)

    net.stop()

if __name__ == '__main__':
    # ipv6Net()
    ipv6NetLinkLocalScopeMultiZone()
