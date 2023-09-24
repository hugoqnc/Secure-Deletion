# Gobra commit 1bc4960
FROM ghcr.io/viperproject/gobra@sha256:0578468fcef0a6f347126253ce535116f55308d513f68ff788353b87c52ae812

RUN apt-get update && \
	apt-get install -y \
    wget \
    jq

# install go
RUN mkdir tmp && \
    cd tmp && \
    wget https://go.dev/dl/go1.17.3.linux-amd64.tar.gz && \
    rm -rf /usr/local/go && tar -C /usr/local -xzf go1.17.3.linux-amd64.tar.gz && \
    cd ../ && \
    rm -rf tmp

# add Go to path:
ENV PATH="${PATH}:/usr/local/go/bin"

COPY wireguard/.modules-precedence ./.modules-precedence
COPY wireguard/conn ./conn
COPY wireguard/device ./device
COPY wireguard/endpoint ./endpoint
COPY wireguard/initiator ./initiator
COPY wireguard/ipc ./ipc
COPY wireguard/library ./library
COPY wireguard/log ./log
COPY wireguard/replay ./replay
COPY wireguard/responder ./responder
COPY wireguard/tai64n ./tai64n
COPY wireguard/tun ./tun
COPY wireguard/verification ./verification
COPY wireguard/go.mod .
COPY wireguard/go.sum .
COPY wireguard/main.go .
COPY wireguard/README.md .
COPY wireguard/docker/compile.sh .
COPY wireguard/docker/test.sh .
COPY wireguard/docker/verify.sh .
COPY wireguard/load-modules.sh .

# copy the reusable verification library
COPY ReusableVerificationLibrary ./ReusableVerificationLibrary

# point Go to local copy of the library:
RUN go mod edit -replace github.com/ModularVerification/ReusableVerificationLibrary=./ReusableVerificationLibrary

# load modules and manually add symlink to reusable verification library:
RUN ./load-modules.sh && \
    mkdir -p .modules/github.com/ModularVerification && \
    ln -s $PWD/ReusableVerificationLibrary .modules/github.com/ModularVerification/ReusableVerificationLibrary

# compile to trigger download of dependent Go packages:
RUN ./compile.sh

# disable entry point specified by the Gobra base container:
ENTRYPOINT []
