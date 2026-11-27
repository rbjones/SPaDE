# Task Description: Python T-expression Layer for the Native Repository

## Purpose and Scope

Build a second Knowledge Repository prototype whose tree representation is based on T-expressions, not S-expressions. Reuse the existing Python NTBS encoding and repository I/O layer. Preserve the existing Python and SML prototypes unchanged.

This task covers T-expression values, their encoding and storage over NTBS, decoding, and focused round-trip tests. It does not cover ProofPower theory export or MCP access.

## Background

The architectural type of T-expressions is specified in [The Theory of T-expressions](../docs/tlcd004.md). A T-expression consists of a byte-sequence label and an ordered finite list of T-expressions. The representation type and `mk_T_ex_rep` in that specification are witnesses used to establish the required algebraic structure; they do not prescribe the repository's storage format.

For efficient WORM storage, persist each T-expression node as its label and references to the sequence numbers of its already-stored child nodes, following the reference-based approach used by the S-expression layer. Do not inline the children or their subtrees: a new node or amendment must be able to reuse existing nodes without duplicating their contents.

The existing Python NTBS codec and repository I/O are in [krcd009.py](krcd009.py). They are the base layer for this prototype and must not be changed. The S-expression layer in [krcd009.py](krcd009.py) and the SML implementation in [krcd011.sml](krcd011.sml) belong to the first prototype and must also remain unchanged.

## Task Requirements

1. Define a Python T-expression node with a byte-sequence label and an ordered list of child repository sequence numbers. Support empty labels, leaf nodes, and arbitrary label bytes.
2. Encode each node as an NTBSS record containing its label followed by the child sequence numbers encoded with the existing integer and sequence-list encoders. Document the record layout. Child expressions must be stored before the parent so all references point backwards in the WORM repository.
3. Store each node record as one byte sequence through the existing Python low-level repository I/O. Provide operations to write a node from its label and child references, and read its label and child references by repository sequence number.
4. Do not recursively encode or duplicate child representations when writing a parent. Allow multiple parents and later amendments to reference the same already-stored child nodes.
5. Reject malformed node records explicitly; do not silently treat them as valid values.
6. Reuse the existing NTBS codec and preserve its behavior, including its handling of embedded zero and one bytes.

## Out of Scope

- Modifying the existing NTBS codec, low-level I/O, or S-expression implementation in Python or SML.
- Replacing or migrating the first prototype.
- Implementing a T-expression layer in SML.
- Completing or changing the ProofPower HOL theory.
- Exporting ProofPower theories, defining repository-level theory structures, or adding MCP operations.

## Deliverables

1. `krcd014.py` — a Python T-expression implementation layered over the existing Python NTBS and low-level I/O interfaces.
2. `krte007.py` — focused unit tests for node records, sequence references, storage, decoding, and malformed input.
3. Update [krci001.mkf](krci001.mkf) to include the new module and tests in the relevant checks.
4. Update this directory's README index with the new implementation, test, and task description entries.

## Acceptance Criteria

1. Each stored node contains its label and ordered child sequence-number references; child representations are not stored inline in the parent.
2. Tests cover leaf nodes, multiple and nested child references, shared children referenced by multiple parents, empty labels, and labels containing embedded `0` and `1` bytes.
3. Writing and reading nodes through the existing repository I/O recovers their labels and child references, including after reopening the repository.
4. Appending a node or amendment that references existing children leaves those child records unchanged and does not duplicate their subtrees.
5. Malformed node records fail explicitly.
6. The existing Python NTBS and S-expression tests continue to pass, and the new tests pass.

## Validation

- Run the focused tests and existing Python regression tests:
  - `python -m unittest kr.krte007 kr.krte003`
- Run the Knowledge Repository build and test target in the project environment:
  - `make -C kr -f krci001.mkf test`

## References

- [The Theory of T-expressions](../docs/tlcd004.md) — architectural type and formal representation.
- [SPaDE Native Repository I/O](krdd004.md) — existing NTBS and repository I/O details.
- [krcd009.py](krcd009.py) — existing Python NTBS and low-level repository I/O implementation.
- [krtd000.md](krtd000.md) — Knowledge Repository meta-task description.
