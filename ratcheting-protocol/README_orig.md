# Wireguard

## Verifying Initiator & Responder
Change into the directory `case_studies/wireguard/src`. All subsequent commands are assumed to be executed in this directory.
To verify the initiator's implementation, run:
```
java -Xss128m -jar <PATH TO GOBRA JAR> -I initiator -I verification -I ./ --module github.com/ModularVerification/casestudies/wireguard -i initiator
```

Similarly, to verify the responder's implementation, run:
```
java -Xss128m -jar <PATH TO GOBRA JAR> -I responder -I verification -I ./ --module github.com/ModularVerification/casestudies/wireguard -i responder
```

Description of the flags:
- `-Xss128m` increases the stack size used to run the verifier. The default argument does not suffice and will cause a runtime exception.
- `-I initiator -I verification -I ./` instructs Gobra to consider the current directory and the `initiator` and `verification` subfolders when performing lookups of imported packages. Note that `initiator` takes precende over `verification` and `verification over the current directory meaning that packages found in these subfolders will be selected over those found in the current directory.
- `--module github.com/ModularVerification/casestudies/wireguard` informs Gobra that we are currently in this module. This impacts the package resolution as it basically means that Gobra will ignore this prefix. For example, the import statement `import lib "github.com/ModularVerification/casestudies/wireguard/library"` results in Gobra looking for the folder `library` in the specified include directories (`-I` option).
- `-i initiator` specifies the package that is verified


## Building & Running this WireGuard Implementation
- `go build -v -o wireguard-gobra` for building the binary
- `./wireguard-gobra -h` will print the usage of all parameters.
- Note that the binary has to be executed with sudo rights if an interface should be created, i.e. `useStandardIO` is set to false.

### Running this WireGuard Implementation with STD I/O
1. `go build -v -o wireguard-gobra` for building the binary
2. Start responder:
  ```
  ./wireguard-gobra \
    --interfaceName utun8 \
    --privateKey oCxC44w/QKqastjiex7OTiKCfJphexquZ3MmJE5upU0= \
    --publicKey poKDYnMyFZWkSwGlAXXb79nh0L8rEb+S8XWAtXQxsmc= \
    --peerPublicKey Y1842DzWWfqP42p9SJNoX1fEJdTOkuyi/fx+1Y7aFU4= \
    --endpoint 127.0.0.1:12345 \
    --port 12344 \
    --useStandardIO
  ```
3. Start initiator:
  ```
  ./wireguard-gobra \
    --interfaceName utun10 \
    --privateKey YIQ1ZXYUVs6OjE2GjDhJgAqoJDaPPdReVtSQ1zOy7n8= \
    --publicKey Y1842DzWWfqP42p9SJNoX1fEJdTOkuyi/fx+1Y7aFU4= \
    --peerPublicKey poKDYnMyFZWkSwGlAXXb79nh0L8rEb+S8XWAtXQxsmc= \
    --endpoint 127.0.0.1:12344 \
    --port 12345 \
    --isInitiator \
    --useStandardIO
  ```
4. Messages can now be entered via standard input. Note however that the initiator is expected to send the first message, then the responder replies with the second message, etc. For the initiator and the responder, messages can be entered at any point, but the entered messages will be forwarded in the aforementioned pattern.


## Running official WireGuard Implementation
### Requirements
1. Clone repo: `git clone https://git.zx2c4.com/wireguard-go`
2. Get Go >= 1.6 (e.g. `brew install go`)
3. Build it: `make`
4. Get Wireguard-Tools (e.g. `brew install wireguard-tools`)

### Demo
The following commands demonstrate how two clients (running on the same machine) can be configured such that a handshake is established and the clients can ping each other via the established tunnel.
Note that the commands have been tested on macOS. The commands for Linux seem to be slightly different and can be seen in [WireGuard's Quick Start](https://www.wireguard.com/quickstart/).

### Run Client 1
1. `sudo ./wireguard-go -f utun6`
2. `wg genkey > client1.private`
3. `sudo ifconfig utun6 inet 192.168.2.1 192.168.2.2`
4. `sudo wg set utun6 private-key ./client1.private`
5. `sudo ifconfig utun6 up`
6. If the first 5 steps for client 2 have been executed, `sudo wg` will display the public keys of each each client
7. `sudo wg set utun6 peer poKDYnMyFZWkSwGlAXXb79nh0L8rEb+S8XWAtXQxsmc= allowed-ips 192.168.2.2/32 endpoint 127.0.0.1:57950` Note that the public key and port have to be adapted based on `sudo wg`'s output
8. `ping 192.168.2.2` pings client 2 which includes performing a handshake
9. `sudo wg` will display the time of the last handshake

### Run Client 2
1. `sudo ./wireguard-go -f utun7`
2. `wg genkey > client2.private`
3. `sudo ifconfig utun7 inet 192.168.2.2 192.168.2.1`
4. `sudo wg set utun7 private-key ./client2.private`
5. `sudo ifconfig utun7 up`
6. If the first 5 steps for client 1 have been executed, `sudo wg` will display the public keys of each each client
7. `sudo wg set utun7 peer Y1842DzWWfqP42p9SJNoX1fEJdTOkuyi/fx+1Y7aFU4= allowed-ips 192.168.2.1/32 endpoint 127.0.0.1:50759` Note that the public key and port have to be adapted based on `sudo wg`'s output
8. `ping 192.168.2.1` pings client 1


## Running this WireGuard Implementation against official WireGuard Implementation
### Run Client 1 (official)
1. `sudo ./wireguard-go -f utun6`
2. `wg genkey > client1.private`
3. `sudo ifconfig utun6 inet 192.168.2.1 192.168.2.2`
4. `sudo wg set utun6 private-key ./client1.private`
5. `sudo ifconfig utun6 up`
6. `sudo wg set utun6 peer poKDYnMyFZWkSwGlAXXb79nh0L8rEb+S8XWAtXQxsmc= allowed-ips 192.168.2.2/32 endpoint 127.0.0.1:12344`

## Run Client 2 (this Implementation)
Use `sudo wg` to get the listening port of client 1 and use it as parameter `--endpoint
```
  sudo ./wireguard-gobra \
    --interfaceName utun8 \
    --privateKey oCxC44w/QKqastjiex7OTiKCfJphexquZ3MmJE5upU0= \
    --publicKey poKDYnMyFZWkSwGlAXXb79nh0L8rEb+S8XWAtXQxsmc= \
    --peerPublicKey Y1842DzWWfqP42p9SJNoX1fEJdTOkuyi/fx+1Y7aFU4= \
    --endpoint 127.0.0.1:62751 \
    --port 12344 \
    --isInitiator
  ```
`sudo ifconfig utun8 inet 192.168.2.2 192.168.2.1`

`ping 192.168.2.1` can then be executed. To ping in the other direction, i.e. `ping 192.168.2.2`, `--isInitiator` has to be dropped from the command above.

