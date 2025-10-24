# Scraping ProofPower HOL Theories into a SPaDE Repository

The ProofPower HOL system has a large and well structured library of theories, which is a good candidate for initial population of a [SPaDE](../docs/tlad001.md#spade) repository, and will serve as a basis for early prototyping of the [SPaDE](../docs/tlad001.md#spade) knowledge repository and deductive intelligence subsystems.
This document describes the process of extracting the content of the ProofPower HOL library into a [SPaDE](../docs/tlad001.md#spade) native repository.

The ProofPower HOL system is implemented in Standard ML.
The theory hierarchy is stored in a PolyML database, and the system provides an API for accessing that database.
This document is primarily concerned with implementation of a procedure in SML which extracts the content of that database and writes it out in the [SPaDE](../docs/tlad001.md#spade) native repository format.

The [SPaDE](../docs/tlad001.md#spade) repository is summarised in [README.md](README.md).

A HOL4 specification of the abstract syntax of the [SPaDE](../docs/tlad001.md#spade) repository is given in [krcd006.sml](krcd006.sml).

The core ProofPower export program is implemented in [krcd005.sml](krcd005.sml).

The Python tooling for interacting with the exported repository is developed in [krcd002.py](krcd002.py) and [krcd003.py](krcd003.py).

The [SPaDE](../docs/tlad001.md#spade) native repository format is described in [SPaDENativeRepo.md](krdd002.md).
