# ProofPower to SPaDE Export Implementation Guide

This document provides implementation guidance for the SML functions required to export ProofPower HOL theories to SPaDE native repositories.

## Files Overview

### 1. `ppexport_signatures.sml`
**Primary signature file** containing all function signatures required for the export process.
- Clean, documentation-ready signatures without implementation stubs
- Includes all required datatypes and exception definitions
- Comprehensive usage documentation
- **Recommended for review and implementation reference**

### 2. `ppexport_sig.sml`  
Formal SML signature definitions structured as signature declarations.
- Organized into logical signature modules
- Provides formal interface contracts
- Useful for modular implementation approach

### 3. `ppexport_impl.sml`
Implementation framework with detailed function stubs and documentation.
- Complete function signatures with parameter names and types
- Detailed implementation guidance for each function
- Structured as SML structures for modular development
- **Recommended starting point for implementation**

### 4. `ppholinterface.md` (updated)
Updated specification document with complete function signatures.
- Added missing SML signatures for repository writing functions
- Includes error handling and validation functions
- Implementation notes and guidance

## Implementation Phases

### Phase 1: ProofPower Interface Functions
Implement functions to access ProofPower theory database:

```sml
(* Core functions - implement first *)
get_theory_names : unit -> string list
get_ancestors : string -> string list  
get_parents : string -> string list
get_defns : string -> (string list * THM) list
get_axioms : string -> (string list * THM) list

(* Object decomposition - implement second *)
dest_thm : THM -> SEQ
dest_simple_type : TYPE -> DEST_SIMPLE_TYPE
dest_simple_term : TERM -> DEST_SIMPLE_TERM
```

### Phase 2: Conversion Functions
Convert ProofPower objects to SPaDE format:

```sml
pp_type_to_htype : TYPE -> htype
pp_term_to_hterm : TERM -> hterm
pp_thm_to_hsequent : THM -> hsequent
```

### Phase 3: Repository Writing
Implement SPaDE repository format writing:

```sml
init_repository : string -> repo_state
write_htype : repo_state -> htype -> repo_state  
write_hterm : repo_state -> hterm -> repo_state
write_theory : repo_state -> string -> (string list * THM) list -> 
              (string list * THM) list -> repo_state
finalize_repository : repo_state -> unit
```

### Phase 4: Export Orchestration
Top-level export coordination:

```sml
topological_sort : string list -> string list
scrape_pp_theories : string -> string list -> unit
scrape_pp_db : string -> unit
```

## Key Implementation Requirements

### 1. ProofPower API Integration
- All `get_*` functions must call corresponding ProofPower system functions
- Handle ProofPower-specific datatypes (TYPE, TERM, THM)
- Manage theory database access and locking

### 2. Format Conversion
- Convert ProofPower concrete syntax to SPaDE abstract syntax
- Map ProofPower type system to SPaDE htype system
- Handle lambda abstractions, applications, and constants correctly

### 3. Repository Format Compliance
- Use postfix notation for repository structure (see `m4002.sml`)
- Write NIL/CONS/Atom structures correctly
- Maintain position tracking for cross-references

### 4. Theory Dependency Management
- Implement topological sorting for theory processing order
- Ensure no theory is processed before its ancestors
- Handle circular dependencies and validation

### 5. Error Handling
- Implement all defined exception types
- Provide descriptive error messages
- Handle ProofPower API errors gracefully

## Testing Strategy

### Unit Testing
Test each function category independently:

1. **ProofPower Interface**: Mock ProofPower database
2. **Conversion Functions**: Test with known ProofPower objects
3. **Repository Writing**: Verify output format compliance  
4. **Integration**: Test complete export workflow

### Validation Testing
- Export small theory hierarchies and verify structure
- Check repository can be read back correctly
- Validate theory dependency ordering
- Test error conditions and exception handling

## Integration Points

### With Existing Code
- `m4001.sml`: Uses SPaDE HOL datatypes (htype, hterm, hsequent)
- `m4002.sml`: Repository serialization format reference
- ProofPower system: Must integrate with existing API

### With Future Development
- Repository reading functions (inverse operations)
- SPaDE knowledge repository access layer
- Deductive kernel integration

## Performance Considerations

- Large theory hierarchies may require streaming
- Memory management for large repository writes
- Progress reporting for long-running exports
- Incremental export capability for updates

## Review Checklist

- [ ] All function signatures match specifications
- [ ] Datatypes compatible with existing SPaDE code
- [ ] Error handling covers all failure modes
- [ ] Repository format matches design specifications  
- [ ] Theory dependency handling is complete
- [ ] Implementation guidance is clear and actionable

## Next Steps

1. **Code Review**: Review signatures for completeness and correctness
2. **Implementation**: Begin with Phase 1 functions
3. **Testing**: Develop test cases parallel to implementation
4. **Integration**: Connect with ProofPower API
5. **Validation**: Test with real ProofPower theories