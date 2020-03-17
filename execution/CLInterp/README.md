# CLVM
(soon to be certified) translation of CL to a stack based intrepreted language CLVM along with an interpreter for CLVM implemented as a contract in the ConCert framework.

## Structure of the project
In [CLIPrelude.v](CLIPrelude.v) we define the datastructures used by CL along with their CLVM equivalents. Since all contracts, environments and traces of transactions must be serializable for the CLVM interpreter, we are required to prove that the involved datatypes are countable and have decideable equality. This is achieved by reduction to other primitive datatypes. CL represents environments, traces and transactions functions, which are not serializable. Therefore we reimplement them as finite maps. This file also combinators for transactions and traces along with interfaces for advancing environments.

In [CLITranslate.v](CLITranslate.v) We define the AST's of CL and the instructions of CLVM along with the semantics of the two languages. We also define the translation from CL to CLVM. The parameters of CLVM are in reverse polish notation. The original CL project can be found here: https://github.com/HIPERFIT/contracts

In [CLInterp.v](CLInterp.v) we automatically derive proofs that all required datatypes are serializable and provide a simple ConCert contract which stores a CLVM contract and result trace. When given an environment it evaluates the contract according to the environment and saves the result.

The tests of the project are locatedd in [CLITest.v](CLITest.v). Since the results of CL and CLVM cannot be compared directly i have inspected the results of the unit tests by hand.