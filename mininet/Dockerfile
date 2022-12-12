FROM ubuntu:18.04

USER root
WORKDIR /root

# macOSでMininetのWalkthrough(http://mininet.org/walkthrough/)をすすめようとして
# このDockerfileを作っていたが、wiresharkが起動できない（GUIがない）ので諦めた


# #############################################################################
# Install dependencies
# #############################################################################
# ref: https://github.com/iwaseyusuke/docker-mininet/blob/main/Dockerfile
RUN apt-get update && apt-get install -y --no-install-recommends \
    curl \
    dnsutils \
    ifupdown \
    iproute2 \
    iptables \
    iputils-ping \
    mininet \
    net-tools \
    openvswitch-switch \
    openvswitch-testcontroller \
    tcpdump \
    vim \
    x11-xserver-utils \
    xterm \
    git \
    ca-certificates \
 && rm -rf /var/lib/apt/lists/*
RUN apt update

# #############################################################################
# Install wireshark
# #############################################################################
# RUN git clone https://github.com/mininet/mininet.git && mininet/util/install.sh -w
RUN git clone https://github.com/mininet/mininet.git
# tshark - Automatically set YES when asked "Should non-superusers be able to capture packets"
# https://askubuntu.com/a/1396918
RUN echo "wireshark-common wireshark-common/install-setuid boolean true" | debconf-set-selections
COPY install.sh mininet/util/install.sh
RUN mininet/util/install.sh -w

EXPOSE 6633 6653 6640

