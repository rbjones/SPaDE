# SPaDE Server for ProofPower Theories

## Introduction

This document is concerned with representing the content of a ProofPower theory hierachy as a SPaDE repository.
It is primarily oriented to the export of ProofPower theories to SPaDE, but it could also be used to make a SPaDE MCP server integrating the content of ProofPower databases into our diasporic repository.

The design is presented as a set of SML signatures with informal descriptions of the intended semantics of the operations in the signatures.
The signatures here are intended to work with those described in [Detail description of Procedures for SPaDE Native Repository I/O](krdd004.md) which provide access to SPaDE repositories in SML.

The requirement addressed here concerns only the export of theories together with any theories upon which they depend to a new SPaDE repository.
It is not concerned with updating an existing SPaDE repository with new content, or with the maintenance of a SPaDE repository as a mirror of continuing developments in a ProofPower database.

## Method

The transcription of theories from a ProofPower database must be done in an order consistent with the parent-child relationships between theories, and the order of extensions in a theory.

In order to undertake export it is therefore necessary to recursively access and export the content of the ancestors of those theories nominated for export.
