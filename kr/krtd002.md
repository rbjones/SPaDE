# Task Description for Code and Test of Low Level Native Repository I/O in SML

## Overview

This task involves implementing and testing the low-level input/output (I/O) operations for the SPaDE Native Repository using Standard ML (SML).
This should replicate in SML the functionality implemented in [krcd008.py](krcd008.py) and [krcd009.py](krcd009.py) together with a wrapper making this service available in python so that it can be delivered as an MCP service.

## Objectives

To prototype the delivery via MCP of access to ITP systems implemented in SML through MCP servers and to provide a first step toward the export of theories from such ITP systems to a SPaDE repositories.

## Input Documents

The following documents provide detailed specifications:

1. krad001.md - Knowledge Repository Architecture Overview
2. krdd002.md - SPaDE Native repository format
3. krdd004.md - Detail description of Procedures for SPaDE Native Repository I/O

Note that only the low-level I/O operations are to be implemented in SML at this stage (under this task).

## Deliverables

1. SML signature document defining the low-level Native Repository I/O interface. (Similar to krcd008.py but in SML).
2. SML implementation of the low-level Native Repository I/O interface. (Similar to krcd009.py but in SML)
3. Unit tests for the SML implementation.
4. Python wrapper (in directory kr) to expose the SML implementation with the same interface as krcd008 and krcd009 so that it can be delivered as an MCP service. This implements the python ABC in krcd008.py using the SML implementation.
5. Integration tests demonstrating the functionality of the SML implementation (in python using the wrapper).  Exactly the same integration tests as for krcd009.py but using the SML implementation via the wrapper.
6. An MCP service delivering the SML Native Repository I/O functionality (in the mcp directory).  This should be similar to the existing MCP service for the python Native Repository I/O but using the SML implementation via the python wrapper.
7. Adapt the test scripts in mcp directory to demonstrate the MCP service functionality through both the python and SML implementations.
8. Amendments to the makefiles in kr and mcp to build and test the new code.
9. Documentation detailing the implementation and usage of the SML Native Repository I/O.

## Notes

All new documents should follow the documentation procedure amms001.md, by allocating document numbers krdd005.md (for the SML signature) and krdd006.md (for the SML implementation) and krte003.md (for the integration tests), and similar for new documents in the mcp directory (mcp/README.doc).
All new documents should be referenced in the relevant README.md files (kr/README.doc and mcp/README.md).

The work should begin with a pull request and should pause after creation of signature documents for review before proceeding to implementation.

Once the SML implementation and its unit tests are complete an analysis of methods for wrapping SML code for use in python should be undertaken to determine the best approach for the python wrapper, and a further review point should be established before proceeding with the wrapper and MCP service implementation.
