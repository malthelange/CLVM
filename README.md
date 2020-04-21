# CLVM 

An interpreter for the DSL for financial contracts called CL, written as a smart contract in the ConCert framework. For serialization the CL language is translated
to a stack based language called CLVM. The goal of this project is to verify the translation in Coq. This repo contains ConCert framework. The CL interpreter is located in execution/CLInterp

## How to build - From the ConCert documentation

Our development works with Coq 8.9.1. and depends on MetaCoq 1.0~alpha+8.9 and
the std++ library v.1.2.1. These dependencies can be installed through
`opam`.

Install Coq (see https://coq.inria.fr/opam-using.html for detailed instructions on how to manage
multiple Coq installations using opam).:

```bash
opam install coq.8.9.1
```

Then MetaCoq:

```bash
opam repo add coq-released https://coq.inria.fr/opam/released
opam install coq-metacoq.1.0~alpha+8.9
```
And std++:

```bash
opam repo add iris-dev https://gitlab.mpi-sws.org/iris/opam.git
opam install coq-stdpp.1.2.1
```

After completing the procedures above, run `make` to build the development, and
`make html` to build the documentation. The documentation will be located in the
docs folder after `make html`.

## Structure of the project 

The [embedding](embedding/) folder contains the development of the embedding.
The [execution](execution/) folder contains the formalization of the smart
contract execution layer, which allows reasoning about interacting contracts.
The [CL Interpreter](execution/CLInterp) folder contains the CL interpreter and theory.