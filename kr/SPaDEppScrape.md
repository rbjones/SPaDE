# Scraping ProofPower HOL Theories into a SPaDE Repository

The ProofPower HOL system has a large and well structured library of theories, which is a good candidate for initial population of a SPaDE repository, and will serve as a basis for early prototyping of the SPaDE knowledge repository and deductive intelligence subsystems.
This document describes the process of extracting the content of the ProofPower HOL library into a SPaDE native repository.

The ProofPower HOL system is implemented in Standard ML.
The theory hierarchy is stored in a PolyML database, and the system provides an API for accessing that database.
This document is primarily concerned with implementation of a procedure in SML which extracts the content of that database and writes it out in the SPaDE native repository format.

The SPaDE native repository format is described in [SPaDENativeRepo.md](SPaDENativeRepo.md).