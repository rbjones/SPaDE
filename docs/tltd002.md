# Task Description: Prepare the SPaDEroot Theory

## Introduction

The task is to write ProofPower HOL specifications to define the SPaDEroot theory.

The details of why we need this theory, the role it will play and the content of the theory are provided in a first draft of the specification document [The SPaDEroot Theory](tlcd002.md).

This theory is an exception to the general pattern of giving the same name to a theory as the document that specifies it.

The definition of the task is effectively split between the task descriptions given here, the text in the draft specification and the standard procedure for creating a new theory in ProofPower HOL (ampd )

This one task description document will be used to cover a sequence of stages in the development of the SPaDEroot theory, all progressive stages in writing the one specification document.

The stages in the task are as follows:

- [Stage 1. The Byte Packing Algorithm](#stage-1-the-byte-packing-algorithm) An explicit (constructive) specification of the preferred algorithm for implementing the *pack_bytes* and *unpack_bytes* functions.

# Stage 1. The Byte Packing Algorithm

The first stage is the detailed specification of the *pack_bytes* function and its inverse.
These have been specified formally in the draft specification document, requiring only that unpack_bytes is the right inverse of pack_bytes.
It is necessary to prove the consistency of that specification by offering a pair of witnesses offering the required behaviour, and it will be convient of these use the inteded algorithm for encoding byte sequences in the SPaDE native repositories.

The task is:

1. to provide the detailed specification of the witnesses pack_bytes_w and unpack_bytes_w
2. use those to prove the existence of functions meeting the specification of pack_bytes and unpack_bytes
3. Store that theorem using the function *save_cs_∃_thm*.
4. Run make build in the docs directory.
5. Check that the load of the SPaDEroot theory succeeds without errors.
6. Analyse failures, if any, and debug the specification or the witnesses accordingly.  Iterate up to three times to clear all errors.
If all errors are cleared, the stage is considered successfully completed.
7. Raise a pull request for the changes to be reviewed and merged into the main branch.