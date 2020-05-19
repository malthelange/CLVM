# CLVM 

An interpreter for the DSL for financial contracts called CL, written as a smart contract in the ConCert framework. For serialization the CL language is translated
to a stack based language called CLVM. The goal of this project is to verify the translation in Coq. This repo contains ConCert framework. The CL interpreter is located in execution/CLInterp

## How to build - From the ConCert documentation

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
opam install coq-bignums
```
And std++:

```bash
opam repo add iris-dev https://gitlab.mpi-sws.org/iris/opam.git
opam install coq-stdpp
```

Install MetaCoq from this [MetaCoq's fork](https://github.com/annenkov/template-coq/tree/coq-8.11-erase-annotated). Follow the instructions from the [official MetaCoq repo](https://github.com/MetaCoq/metacoq#installing-from-github-repository-for-developers).

After completing the procedures above, run `make` to build the development, and
`make html` to build the documentation. The documentation will be located in the
docs folder after `make html`.

## Structure of the project 

The [embedding](embedding/) folder contains the development of the embedding.

The [execution](execution/) folder contains the formalization of the smart
contract execution layer, which allows reasoning about interacting contracts.


The [CL Interpreter](execution/CLInterp) folder contains the CL interpreter and theory.

The [extraction](extraction/) folder contains a printing procedure for the deep embedding into the Liquidity syntax. For extraction using MetaCoq's **certified erasure** see the [extract-cert](https://github.com/AU-COBRA/ConCert/tree/extract-cert) branch (requires [MetaCoq's fork](https://github.com/annenkov/template-coq/tree/coq-8.11-erase-annotated) to compile).

## Notes for developers

The [execution](execution/) subproject can be built independently via running `make` in the `execution` folder. This also means that the `_CoqProject` file inside the `execution` folder musdt be manually kept in sync with the main `_CoqProject` in the root.

