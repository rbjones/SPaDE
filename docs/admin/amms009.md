# Agentic development team

The project manager looks after the administrative documents in this directory, writing them directly or by delegation. Delegation of an admin document follows [ampd009.md](ampd009.md).

Roles are functions. A human or an agent may fill one. While a subsystem is small, one agent may hold more than one of its functions. The responsibility stays with the function.

## Roles

| Role | Scope |
| --- | --- |
| Principal | Supports the architect on top-level strategy. Accepts work into `main`. |
| Philosopher | Synthetic philosophy at docs level: purpose, norms, and the concepts the architecture has to bear. |
| Architect | Docs-level architecture. Top-level strategy, with the principal's support. Technical strategy that states architectural commitments. |
| Project manager | How the team works, how the Spark is occupied, the software baseline, and the breakdown of work into tasks one role can finish. |
| Subsystem detailed design | Detailed design of one subsystem. |
| Subsystem implementation | Implementation of that subsystem, including its formal specifications. |
| Subsystem test | Test of that subsystem. |
| Knowledge onboarding | Autoformalising declarative knowledge into [SPaDE](../tlad001.md#spade) repositories. Staffed after formal development has moved into those repositories. |
| Focal trainer | Continuous training on layered [perfect information spaces](../tlad001.md#perfect-information-space). Staffed when those spaces are ready to run. |

The subsystems are the knowledge repository, the deductive kernel, deductive intelligence, and the MCP server. Each has its own detailed design, implementation, and test.

Further roles are added when the architect's strategy names them.

## Where the work is written

| Matter | Series or directory |
| --- | --- |
| Philosophy | `docs/tlph*` |
| Strategic planning | `docs/admin/ampl*` |
| Architecture, and technical strategy that states an architectural interface | `docs/tlad*` |
| Administration, team operation, commissioning | `docs/admin/` |
| Detailed design, implementation, and test | The subsystem directory (`kr/`, `dk/`, `di/`, `mcp/`) |
| Onboarded formal knowledge | [SPaDE](../tlad001.md#spade) repositories, once they hold the formal development |

Traditional coding is a thin support for the host software. It is not the main body of the work.

## Architecture and design

An interface is architecture when it is exported for other projects to engage with, or when it involves more than one subsystem. The same interface may be both. Architecture is documented in the `tlad` series.

Detailed design remains in the subsystem directory. Material that states an architectural interface and currently lives in a subsystem, including `kr/`, is promoted to `tlad`. That promotion is the architect's work.

## Who fills a role

Local agents on this DGX Spark do as much of the development as they can. Grok and Copilot in the cloud are used where the most powerful models are likely to be beneficial. Commissioning and review are in [ampd009.md](ampd009.md). The order of the work is in [ampl006.md](ampl006.md). The first three local roles, project manager, architect, and philosopher, are briefed for trial in [amms011.md](amms011.md).

Two kinds of local model are provided for, as in [amms010.md](amms010.md):

- A specification model, which writes formal specifications of SPaDE and its subsystems for the first prototypes. Until SPaDE can check HOL specifications, those specifications are checked with ProofPower.
- An MCP model, which progresses the theory hierarchy in SPaDE repositories through the MCP interface. That interface is abstract syntax as JSON. SPaDE does not take concrete syntax.

---

Document ID: amms009
Author: Grok Build (Grok 4.7)
Status: In progress
Chat log: [amcl003.md](amcl003.md)
