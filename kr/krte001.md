# Knowledge Repository Prototyping Strategy

## Document Information
- **Document ID**: krte001.md  
- **Version**: 1.0
- **Date**: 15 October 2025
- **Author**: Analysis based on existing SPaDE codebase
- **Status**: Ready for Review

## Executive Summary

This document outlines the development strategy for the SPaDE Knowledge Repository prototype, consisting of two separate programs:

1. **SML ProofPower Scraper** - Offline batch process to extract ProofPower theories into SPaDE repositories
2. **Python MCP Server** - Online service to query and browse SPaDE repositories via MCP protocol

## Architecture Overview

### Program Separation
The prototype consists of two independent programs connected only through the SPaDE repository file format:

```
ProofPower DB → [SML Scraper] → SPaDE Repository File → [Python MCP Server] → MCP Clients
```

### Key Design Principle
The scraping is an **offline batch activity**, completely separate from the MCP server operations. The MCP server only needs to read pre-generated repository files.

## Program 1: SML ProofPower Scraper

### Purpose
Extract ProofPower HOL theory hierarchies and convert them to SPaDE native repository format.

### Current Implementation Status
- **krcd001.sml**: Basic CONS cell serialization (COMPLETE)
- **krcd005.sml**: HOL datatype definitions (COMPLETE)  
- **krcd005.sml**: Repository export functions (PARTIAL)

### Required Development Work

#### 1. ProofPower Interface Functions
```sml
(* Core ProofPower API calls - these need to be implemented *)
fun get_theory_names(): string list
fun get_parents(theory: string): string list  
fun get_ancestors(theory: string): string list
fun get_theory_signature(theory: string): signature
fun get_theory_axioms(theory: string): hterm list
```

#### 2. Theory Processing Pipeline
- Sort theories by dependency order (no theory appears before its parents)
- Extract each theory's signature and constraints
- Convert ProofPower HOL structures to SPaDE format
- Handle HOL literals vs SPaDE literals appropriately

#### 3. Repository Generation
- Create SPaDE native repository file structure
- Write theories in dependency order
- Generate CONS cell linkages with backward pointers
- Create top-level repository folder structure (version "1")

#### 4. Main Entry Point
```sml
fun scrape_proofpower_to_spade(output_file: string): unit
```

### Implementation Priority: HIGH
This is the foundation that enables everything else.

### Estimated Effort: 2-3 weeks
Mainly ProofPower API integration and theory traversal logic.

## Program 2: Python MCP Server

### Purpose  
Provide MCP-based access to SPaDE repositories for querying, browsing, and inspection.

### Current Implementation Status
- **krcd003.py**: Basic CONS cell reading (COMPLETE)
- **krcd002.py**: HOL datatype Python classes (COMPLETE)
- **spade-mcp/**: MCP server template copied from p01 (READY)

### Required Development Work

#### 1. Repository Reader Interface
```python
class SPaDERepository:
    def __init__(self, repo_file: str)
    def load_repository(self) -> None
    def search_theories(self, pattern: str) -> List[str]
    def get_theory(self, name: str) -> Theory
    def validate(self) -> bool
```

#### 2. Theory Navigation
```python
class Theory:
    def __init__(self, name: str, parents: List[str], signature: dict, constraints: List[str])
    def get_dependencies(self) -> List[str]
    def find_definition(self, name: str) -> Optional[Definition]
```

#### 3. MCP Tools Implementation
```python
async def query_repository(pattern: str, search_type: str) -> str
async def inspect_theory(theory_name: str) -> str  
async def browse_context(theory_name: str) -> str
async def validate_repository() -> str
async def get_definition(name: str) -> str
```

#### 4. Performance Optimization
- Cache frequently accessed repository components
- Efficient CONS cell navigation
- Memory management for large repositories

### Implementation Priority: MEDIUM
Can be developed in parallel with SML scraper using mock data.

### Estimated Effort: 1-2 weeks
Mainly query optimization and MCP tool implementation.

## Integration Requirements

### File Format Compatibility
Both programs must implement the SPaDE native repository binary format:
- CONS cells with backward pointers (as per krdd002.md)
- Null-terminated byte sequences with binary 1 as escape character
- Repository versioning structure

### Data Structure Agreement  
Both must handle identical HOL datatype representations:
- hterm, htype structures from krcd002.py/krcd005.sml
- Name resolution (rname, sname)
- Theory signatures and constraints

### Testing Strategy
- Use small ProofPower theories for end-to-end validation
- Create test repository files for MCP server development
- Validate round-trip: ProofPower → SPaDE → Query results

## Current Assessment: STRONG FOUNDATION

### Strengths
- Repository format is well-specified in documentation
- Basic serialization code exists for both SML and Python  
- HOL datatypes are defined in both languages
- MCP server template is proven working
- Clear separation of concerns between offline and online components

### Implementation Gaps
- **SML**: Need actual ProofPower API calls and theory traversal
- **Python**: Need efficient repository parsing and caching  
- **Both**: Need comprehensive error handling and validation

### Risk Assessment: LOW
- Architecture is sound and well-documented
- Foundation code exists and is testable
- Development can proceed incrementally
- No major technical blockers identified

## Development Roadmap

### Phase 1: Foundation (Week 1-2)
- Complete SML ProofPower interface functions
- Implement basic Python repository loading
- Create end-to-end test with minimal theory

### Phase 2: Core Functionality (Week 3-4)  
- Complete SML scraper for theory hierarchies
- Implement all MCP tools in Python server
- Performance optimization and caching

### Phase 3: Testing & Refinement (Week 5)
- Comprehensive testing with real ProofPower theories
- Error handling and edge case coverage
- Documentation and deployment preparation

## Next Steps for Review

1. **Validate Architecture**: Confirm the program separation and data flow
2. **Review Implementation Plan**: Assess development priorities and timeline
3. **Identify Dependencies**: Confirm ProofPower API availability and documentation
4. **Resource Allocation**: Determine development focus areas

## Conclusion

The SPaDE Knowledge Repository prototype is well-positioned for implementation. The existing codebase provides a solid foundation, the architecture is sound, and the development path is clear. 

**Recommendation: Proceed with implementation focusing on SML scraper first, followed by Python MCP server development.**

---

*This document should be reviewed and updated based on implementation experience and changing requirements.*