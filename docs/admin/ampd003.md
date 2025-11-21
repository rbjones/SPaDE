# Conversational Documentation Development Procedure

**Document ID**: ampd003  
**Status**: Draft  
**Author**: GitHub Copilot  (Claude Sonnet 4.5)
**Date**: 2025-11-17  
**Related Chat Log**: [amcl001.md](amcl001.md)

## Purpose

This procedure describes the process for developing high-level documentation (particularly philosophical and architectural materials) through conversational interaction between a client and an agent. This approach is especially valuable when a simple task description is inadequate and exploratory discussion is needed to clarify concepts, approach, and scope before writing can begin.

## Applicability

This procedure is applicable to:

- High-level philosophical and architectural documentation
- Documents requiring conceptual exploration before drafting
- Revision and refinement of existing documents
- Creation of multiple interconnected documents
- Any agentic task appropriately initiated and guided conversationally

## Roles

- **Client**: The party initiating the documentation request (human or potentially AI)
- **Agent**: The party facilitating the discussion and creating the documentation (LLM, human, or other AI system)

## Procedure

### 1. Session Initiation

The client initiates a new chat session with the following information:

0. "Hi *agent name* this is *client name*" this gives the short names to be used in the transcript. Full names should only be used in the header of the transcript including the model name for copilot.
1. Reference to this procedure document (ampd003)
2. Target directory (e.g., `docs/`, `kr/`, `dk/`)
3. Subsystem code (e.g., `tl` for docs, `kr` for knowledge repository)
4. Document type code (e.g., `ph` for philosophical, `ad` for architectural design)
5. Provisional title for the document

The agent should identify itself including the underlying model name (e.g., "GitHub Copilot (Claude Sonnet 4.5)").

**Example initiation**:
> "Following ampd003, I'd like to create a new philosophical document in docs/ about reflexive reasoning. My name is Roger Jones."

### 2. Setup Stage

The agent performs the following setup tasks:

1. **Determine document number**:
   - Check target directory's README.md
   - Find next available number for specified document type
   - Construct filename (e.g., `tlph011.md`)

2. **Create target document**:
   - Create file with title but no header. A footer will be created later.
   - Update directory README.md index

3. **Create chat log**:
   - Co-locate with target document
   - Find next available chat log number (type code `cl`)
   - Construct filename (e.g., `tlcl001.md` in same directory)
   - Create file with header only
   - Include:
     - Document ID
     - Full client name
     - Agent name (including model, e.g., "GitHub Copilot (Claude Sonnet 4.5)")
     - Link to target document(s)
     - Purpose/topic
   - Update directory README.md index

4. **Confirm setup**:
   - Report created files and locations
   - Ready for discussion

### 3. Discussion Phase

**Objectives**:

- Explore the topic through dialogue
- Probe agent's knowledge of relevant concepts
- Clarify approach and scope
- Identify key matters to be covered
- Build shared understanding

**Process**:

- Client leads exploration with questions and discussion
- Agent responds with relevant knowledge and insights
- Free-form, exploratory conversation
- Agent updates chat log incrementally after each exchange
- Agent writes **nothing** to target document until explicitly requested

**Chat Log Updates**:

- Full transcript of conversation
- Written incrementally by agent
- No client request needed for log updates
- Maintains currency throughout session
- Agent reformats client contributions for readability:
  - head each contribution with the short name of the contributor as given in the opening of the session, in bold rather than sections heading, and omitting the role.
  - Add markdown structure (lists, paragraphs, appropriate emphasis)
  - Break long blocks into logical paragraphs
  - Preserve meaning and literal text, while improving presentation
  - Match formatting style of agent's own contributions where appropriate
  
### 4. Drafting Phase

**Initiation**:

- Begins only when client explicitly requests drafting
- Client confirms sufficient understanding has been reached

**Process**:

1. Client requests initial draft or specific content
2. Agent confirms understanding of requirements
3. Agent creates/updates target document content
4. Agent continues updating chat log

**Content**:

- Agent writes document content as requested
- Maintains document structure and formatting standards
- Updates document status as appropriate

### 5. Review and Refinement

**Continuation**:

- Client may return at any time to request changes
- Discussion continues in same chat session if available
- If chat history unavailable, agent reads saved chat log to resume context

**Process**:

1. Client reviews document content
2. Client requests specific changes or enhancements
3. Agent and client discuss changes conversationally
4. Agent confirms understanding before implementing
5. Agent updates both target document and chat log
6. Cycle repeats as needed

**Chat Log Continuity**:

- Continuing discussion appends to existing log
- Maintains complete history across sessions
- Links discussion to corresponding document changes

### 6. Completion

**Status Updates**:

- After completion of the document content a footer should be added. The footer should include:
  - Document ID
  - Author: Agent name (including model, e.g., "GitHub Copilot (Claude Sonnet 4.5)")
  - Link to chat log (to be created)
  - Status is either "Stable" (when the client closes the conversation) or "In progress" before that, or after the client reopens it.  If requested by the client on closing a conversation the status may be set to some other word or phrase as requested.

**Traceability**:

- Target document links to chat log
- Chat log links to target document(s)
- Full conversational history preserved
- Provides context for future reference and updates

## Multiple Documents

This procedure can be used to create or modify multiple related documents in a single conversation:

- Agent creates/updates all specified documents
- Single chat log references all target documents
- Each target document references the shared chat log
- Maintains coherent narrative across related materials

## Best Practices

### For Clients

- Provide clear context and objectives at session start
- Explore thoroughly before requesting drafts
- Confirm understanding before asking agent to write
- Use same chat session for related updates when possible
- Request explicit status changes when documents are ready

### For Agents

- Create clean document structures during setup
- Update chat log incrementally throughout session
- Wait for explicit instruction before writing to target documents
- Confirm understanding of requirements before implementing
- Maintain cross-references between logs and documents
- Preserve full conversational context in logs
- In conversation keep the interchanges brief, if there is much to discuss, list the items first and then go through them one by one in separate exchanges.  Concision is always important, padding obscures the key issues, if needed clarification can be sought.

## Notes

- This procedure emphasizes the conversational nature of high-level documentation development
- The chat log provides valuable context for understanding document evolution
- The process is agent-agnostic and client-agnostic (human or AI)
- Incremental log updates ensure continuity and traceability
- Explicit client control over target document writing ensures alignment with intent
