# Task Description: Python ABC for SPaDE Native Repository I/O

**Document ID**: krtd001.md  
**Category**: Task Description  
**Subsystem**: kr (Knowledge Repository)  
**Status**: Ready for implementation

**Related Documents**:

- [krdd004.md](krdd004.md) - Detailed Design (**READ THIS FIRST**)
- [amms008.md](../docs/admin/amms008.md) - Python ABC Coding Standards

## Objective

Create Python Abstract Base Classes that define interfaces for SPaDE native repository I/O operations per [krdd004.md](krdd004.md) Section 3 (Modules):

1. **EncoderDecoder** (Section 3.1) - 8 abstract methods for encoding/decoding operations
2. **RepositoryIO** (Section 3.2) - 8 abstract methods for file and cache operations
3. **SExpressionIO** (Section 3.3) - 4 abstract methods for S-expression operations

## Approach

This task follows a two-phase approach to ensure design clarity:

### Phase 1: Draft ABC for Review

Create `kr/krcd008.py` containing:

- Three ABC classes with method signatures based on [krdd004.md](krdd004.md)
- Comprehensive docstrings per [amms008.md](../docs/admin/amms008.md) standards
- **Implementation questions** in docstrings where [krdd004.md](krdd004.md) is ambiguous:
  - Data structure choices (cache implementation, stack type)
  - Error handling strategy (exceptions to raise)
  - Edge case behavior (empty files, invalid input)
  - Type constraints (integer sizes, string encoding)
- **Suggestions** for answers to the questions raised and for where to document those details (design doc vs ABC docstrings)

Submit Phase 1 deliverable for review before proceeding to Phase 2.

### Phase 2: Final ABC (after review approval)

Once Phase 1 is reviewed and design decisions made:

- Update `kr/krcd008.py` with agreed method signatures and resolved questions
- Update [krdd004.md](krdd004.md) with clarifications if needed
- Create `kr/test_krcd008.py` with tests per [amms008.md](../docs/admin/amms008.md)
- Add `krcd008.py` to `PYABCFILES` in `kr/krci001.mkf`

## Validation

### Phase 1 Complete When

- [ ] Draft ABC has all required methods with type hints
- [ ] Docstrings identify ambiguities and propose solutions
- [ ] Suggestions provided for documentation locations
- [ ] Code passes: `python -m py_compile kr/krcd008.py`

### Phase 2 Complete When

- [ ] All implementation questions resolved
- [ ] `make -f kr/krci001.mkf test` passes all checks
- [ ] Follows [amms008.md](../docs/admin/amms008.md) validation checklist

## Notes

- This task produces **interface definitions only** - no implementation
- Concrete implementation will be in separate task (krtd002.md)
- Phase 1 is designed to surface design ambiguities early
- Design decisions made during review will inform implementation phase
