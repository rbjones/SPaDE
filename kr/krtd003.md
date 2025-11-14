# Task Description: SML Signatures for SPaDE Native Repository I/O

**Document ID**: krtd003.md  
**Category**: Task Description  
**Subsystem**: kr (Knowledge Repository)  
**Status**: Ready for implementation

**Related Documents**:

- [krdd004.md](krdd004.md) - Detailed Design (**READ THIS FIRST**)

## Objective

Create SML signatures that define interfaces for SPaDE native repository I/O operations per [krdd004.md](krdd004.md) Section 3 (Modules):

1. **EncoderDecoder** (Section 3.1) - 8 function signatures for encoding/decoding operations
2. **RepositoryIO** (Section 3.2) - 8 function signatures for file and cache operations
3. **SExpressionIO** (Section 3.3) - 7 function signatures for S-expression operations (including stack operations)

## Approach

This task follows a two-phase approach to ensure design clarity:

### Phase 1: Draft Signatures for Review

Create `kr/krcd010.sml` containing:

- Three SML signatures with function specifications based on [krdd004.md](krdd004.md)
- Comprehensive comments documenting each function
- **Implementation questions** in comments where [krdd004.md](krdd004.md) is ambiguous:
  - Data structure choices (cache representation, stack type, repository handle)
  - Exception specifications (which exceptions to raise, when)
  - Edge case behavior (empty files, invalid input, corrupted data)
  - Type constraints (string vs bytes, integer representation)
  - ProofPower-specific considerations (MESSAGE vs custom exceptions)
- **Suggestions** for answers to the questions raised and for where to document those details (design doc vs signature comments)

Submit Phase 1 deliverable for review before proceeding to Phase 2.

### Phase 2: Final Signatures (after review approval)

Once Phase 1 is reviewed and design decisions made:

- Update `kr/krcd010.sml` with agreed function signatures and resolved questions
- Update [krdd004.md](krdd004.md) with clarifications if needed
- Create basic test harness demonstrating signature usage
- Add `krcd010.sml` to `PPHOLSMLFILES` in `kr/krci001.mkf`

## Technical Details

### SML Signature Structure

Each module should be defined as an SML signature:

```sml
signature ENCODER_DECODER = sig
    (* Type definitions *)
    type byte_seq = Word8Vector.vector
    
    (* Function specifications with comments *)
    val encode_bytes : byte_seq -> byte_seq
    (* Encode byte sequence with escape convention (byte 1 as escape) *)
    
    val decode_bytes : byte_seq -> byte_seq
    (* Decode null-terminated sequence removing escapes *)
    
    (* ... additional functions *)
end;
```

### ProofPower Environment

- Target: ProofPower HOL (pp-ml)
- Use ProofPower standard libraries where appropriate
- Follow ProofPower coding conventions
- Consider ProofPower's exception handling (MESSAGE type)

### Module Organization

All three signatures in single file `kr/krcd010.sml`:

- `signature ENCODER_DECODER`
- `signature REPOSITORY_IO`  
- `signature SEXPR_IO`

## Validation

### Phase 1 Complete When

- [ ] Draft signatures have all required function specifications
- [ ] Comments identify ambiguities and propose solutions
- [ ] Suggestions provided for documentation locations
- [ ] Type definitions are appropriate for ProofPower
- [ ] Code passes: ProofPower syntax check (can be loaded without structure implementation)

### Phase 2 Complete When

- [ ] All implementation questions resolved
- [ ] Signatures compile without errors in ProofPower
- [ ] Documentation updated as needed
- [ ] Added to makefile for tracking

## Notes

- This task produces **interface definitions only** - no implementation structures
- Concrete implementation structures will be in separate task (krtd004.md)
- Phase 1 is designed to surface design ambiguities early
- Design decisions made during review will inform implementation phase
- Focus on low-level repository I/O for writing repositories from ProofPower theories
