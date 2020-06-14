# CLVM
Certified translation of CL to a stack based intrepreted language CLVM along with an interpreter for CLVM implemented as a contract in the ConCert framework. This is the code used in the master thesis "Certified compilation from a financial contract DSL to smart contract languages" by Malthe Lange.

## Structure of the project
The project has not been refactored in a long time due to time constraints. In previous iterations of the code we wanted to present two different interpreters for CLVM. CLVMI which is described in the thesis, and CLVMP. CLVMP is faulty and is not considered a part of the final system, yet it has left some artefacts in the codebase we did not have the time to remove. Namely the "partial" flag in the stack based interpreter. In CLVMI this is always false. The of types and functions are a little bit different than the ones used in the theis, but it should be intuitive to read anyway. The project consits mainly of the 3 following files:


In [CLIPrelude.v](CLIPrelude.v) we define the datastructures used by CL along with their CLVM equivalents. Since all contracts, environments and traces of transactions must be serializable for the CLVM interpreter, we are required to prove that the involved datatypes are countable and have decideable equality. This is achieved by reduction to other primitive datatypes. CL represents environments, traces and transactions functions, which are not serializable. Therefore we reimplement them as finite maps. This file also defines combinators for transactions and traces along with interfaces for advancing environments. This file also states and proves theorems of the environment representations.

In [CLITranslate.v](CLITranslate.v) We define the AST's of CL and the instructions of CLVM along with the semantics of the two languages. We also define the translation from CL to CLVM. The original CL project can be found here: https://github.com/HIPERFIT/contracts. We also prove that compiled and interpreted CL contracts follow the semantics of the original CL contract.

In [CLInterp.v](CLInterp.v) we automatically derive proofs that all required datatypes are serializable and provide a financial contract evaluator based on CLVMI. When given an environment it evaluates the contract according to the environment and saves the result.

