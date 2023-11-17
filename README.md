# Secure Deletion of Sensitive Data in Protocol Implementations
**Master's Thesis — ETH Zürich — Hugo Queinnec — 2023**

[![Hello](https://img.shields.io/badge/read%20the%20report-blue?style=for-the-badge&logo=none)](https://doi.org/10.3929/ethz-b-000641727)

## Abstract
  Security protocols are crucial for protecting sensitive information and communications in today's digital age. Even a minor flaw in how these protocols are implemented can lead to serious consequences.
  Hence, proving the implementations secure is attractive as we prove the absence of such flaws.

  Arquint et al. propose a generic and modular methodology to verify the security of protocol implementations.
  We extend their methodology to reason about ephemeral and time-sensitive data, which must be deleted within certain time frames.
  This enhancement allows us to verify strong security properties, such as forward secrecy and post-compromise security, for protocols that frequently renew their keys, such as Signal.
  Our contributions encompass a conceptual expansion of their methodology and an extension of their Go library, which simplifies the verification of protocol implementations in Go.
  A case study, featuring a Signal-like protocol implementation, showcases expressiveness and practical applicability of our methodology extension.

## Repository
This repository contains the source code associated to this Master's thesis, as well as the Latex source files of the project description and the final report.
It is organized as follows:
- [`library`](./library/) contains the source code of the extended Reusable Verification Library in Go.
- [`ratcheting-protocol`](./ratcheting-protocol) contains the source code of the full ratcheting protocol implementation (and specification) in Go. As explained in the report, this implementation is not yet complete.
- [`report`](./report/) contains the Latex source files of the final report.
- [`description`](./description/) contains the Latex source files of the project description.
