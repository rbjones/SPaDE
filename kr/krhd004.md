# ProofPower Database Scraping

## Contents

## Introduction

This document is primarily intended to describe how theories from a ProofPower database can be copied into a new SPaDE native repository.

This is to be done by SML code which executes in ProofPower, reading the theories from the ProofPower database using the procedures enumerated in [krdd001.md](krdd001.md) and writing the theories into a new SPaDE native repository using the procedures described in [krdd004.md](krdd004.md) and implemented as [krdd011.sml](krdd011.sml) (signatures) and [krdd011.sml](krdd011.sml) (structures).

## Requirement

The requirement is to be able to copy theories from a ProofPower database into a new SPaDE native repository, in such a way that the resulting SPaDE native repository is a faithful representation of the original ProofPower database, and that the resulting SPaDE native repository can be used as the basis for further development in SPaDE.

A function is required which takes the name for a new SPaDE native repository, and the name of a theory in the ProofPower database, and copies that theory and all of its dependencies into the new SPaDE native repository.

A difficulty in the transcription is the different structure of the namespaces between ProofPower and SPaDE.
Each ProofPower theory results in a flat namespace which aggregates the names introduced in its ancestors with those introduced in the theory.
The same name may appear in more than one theory in a ProofPower database, provided that the defining theories are unrelated so that no name clash arises.
In SPaDE we have a hierarchical namespace, the names of constants being determined by the path to the theory in which they are defined, and the name of the constant within that theory.  Constant names in terms are relative, giving the path from the nearest common ancestor of the defining theory and the using theory, to the defining theory, and then the name of the constant within that theory.
When transcribing a ProofPower theory hierarchy into a SPaDE native repository, a flat structure will be required in which all theories appear in the top level folder (the relevant commit of the appropriate branch of the repository), and the names of the constants in the theories are determined by the path to the defining theory, which is either a simple constant the reference is in the defining theory, or a one step elevation the name of the theory which defined the object, and the name of the constant within that theory.

The translation of type constructors and constants in the ProofPower theory for use in the corresponding SPaDE theory requires a mapping to be created as the transcription progresses, recording the for each constant the name of the theory in which it was defined.
This will enable a correct relative reference to the constant to be generated for each subsequent use of the constant.
The reference will be the simple name of the constant for any use of the constant in its defining theory, and will be the name of the defining theory and the name of the constant within that theory for any use of the constant in a different theory.
