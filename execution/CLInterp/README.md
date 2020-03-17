#CLVM - (soon to be certified) translation of CL to a stack based intrepreted language CLVM along with an interpreter for CLVM implemented as a contract in the ConCert framework.

## Structure of the project
In [CLIPrelude.v](CLIPrelude.v) we define the datastructures used by CL along with their CLVM equivalents. Since all contracts, environments and traces of transactions must be serializable for the CLVM interpreter, we are required to prove that the involved datatypes are countable and have decideable equality. This is achieved by reduction to other primitive datatypes. CL represents environments, traces and transactions functions, which are not serializable. Therefore we reimplement them as finite maps. This file also combinators for transactions and traces along with interfaces for advancing environments.

In 
