# Scraping ProofPower HOL Theories into a SPaDE Repository

The ProofPower HOL system has a large and well structured library of theories, which is a good candidate for initial population of a SPaDE repository, and will serve as a basis for early prototyping of the SPaDE knowledge repository and deductive intelligence subsystems.
This document describes the process of extracting the content of the ProofPower HOL library into a SPaDE native repository.

The ProofPower HOL system is implemented in Standard ML.
The theory hierarchy is stored in a PolyML database, and the system provides an API for accessing that database.
This document is primarily concerned with implementation of a procedure in SML which extracts the content of that database and writes it out in the SPaDE native repository format.

The SPaDE repository is described in [KnowledgeRepo.md](KnowledgeRepo.md).

A HOL4 specification of the abstract syntax of the SPaDE repository is given in [h4001.md](h4001.md).

The process of scraping a ProofPower HOL theory database into a SPaDE repository is described in [SPaDEppScrape.md](SPaDEppScrape.md).

The procedural interface for accessing the ProofPower HOL database is described in [m4002.md](m4002.md).

The SPaDE native repository format is described in [SPaDENativeRepo.md](krdd002.md).
