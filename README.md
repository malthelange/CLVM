# CLVM 

An interpreter for the DSL for financial contracts called CL, written as a smart contract in the ConCert framework. For serialization the CL language is translated
to a stack based language called CLVM. The goal of this project is to verify the translation in Coq. This repo contains is a fork of the ConCert framework. The additions made by our CLVM project is found in
[CLVM](execution/CLInterp). The readme of the folder details the CLVM project structure.

## How to build
This is the build procedure described by the developers of the ConCert framwork. 

Our development works with Coq 8.11. and depends on MetaCoq 1.0~alpha2+8.11,
std++ and coq-bignums. These dependencies can be installed through `opam`.

Install Coq (see https://coq.inria.fr/opam-using.html for detailed instructions on how to manage
multiple Coq installations using opam).:

```bash
opam install coq.8.11
```

Then MetaCoq and bignums:

```bash
opam repo add coq-released https://coq.inria.fr/opam/released
opam install coq-metacoq.1.0~alpha+8.11
opam install coq-bignums
```
And std++:

```bash
opam repo add iris-dev https://gitlab.mpi-sws.org/iris/opam.git
opam install coq-stdpp
```

To build this project run "make" in the [execution](execution/) folder.
## Structure of the project 

The [embedding](embedding/) folder contains the ConCert development of the embedding.
The [execution](execution/) folder contains the ConCert formalization of the smart contract execution layer, which allows reasoning about interacting contracts.

The [CLVM](execution/CLInterp) folder contains the CLVM compilation scheme and theory.