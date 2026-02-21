# SPaDE Project Action Plan

## Preliminary Notes

I completely scrapped the AI generated action plan!
Not surprisingly, it was a million miles from my reality.
This is not a "Waterfall" type development, i.e. its not going to progress from the top down in orderly steps.

I did want to put together some good top level accounts of what I am trying to do so that agentic AI might be better able to assist me, but that's real hard to do and I need to get [spade](../tlad001.md#spade)s in the ground and go back to that later.

## Some Key Features of the Architecture

### Delivery as MCP server(s)

On digging down to explore what can be prototyped ASAP, I arrived at greater clarity on some architectural features which can be prototyped early on.

It was always my intention that this project would not be involved in "user interfaces", and in particular, concrete syntax (though inevitably would have some engagement with concrete representations for storage).
The intention was that [SPaDE](../tlad001.md#spade) would be a tool for AIs, and that insofar as humans access the knowledge repository their access would be mediated by LLMs or subsequent generations of agentic AI.

I am now able to make that more definite, insofar as I am now acquainted with the mechanisms which that would involve, and it looks like [SPaDE](../tlad001.md#spade) capabilities will be delivered through an MCP server.
Those capabilities may ultimately embrace the whole of what I am calling "[focal engineering](../tlad001.md#focal-engineering)", which is to say the solution of problems in perfect information spaces using formal models and derivatives of alpha-zero methods.

### Some Prototype-Relevant Architecture

Three parts of the project represent something of an onion, the knowledge repository at the core, the deductive kernel moving us from storage to inference, and the "deductive intelligence" which uses [focal AI](../tlad001.md#focal-intelligence-or-focal-ai) to achieve intelligent formally verified design.
All this embedded in user facing agentic LLM which elicits user requirements casting them behind the scenes as formal models and requirements specifications providing a basis for formally verified design and implementation.

The prototyping can progress from the inside od the onion out, but from the very beginning will seek to establish the delivery of its rudimentary capabilities through MCP servers (providing early evaluation of their suitability).

## Initial Prototyping Steps

As I write, I have first formal specifications of the logical structure of the knowledge repository as recursive datatypes in HOL4.
Copilot has recast this in SML and Python.
This will mediate in the transfer of theory hierarchies from ProofPower HOL (in the first instance) and HOL4 later into [SPaDE](../tlad001.md#spade) repositories.

This will take place in two steps, the first being the extraction of the theory hierarchy into an ML structure corresponding to the logical structure of the [SPaDE](../tlad001.md#spade) repository.
This will provide a first check on whether the structure is satisfactory, and may result in some evolution of that structure.
The second step will be to linearise this abstract structure for saving in a file which will be the stored form of the repository.

We are then in a position to prototype a read-only MCP permitting read access to this repository.
In the first instance this is likely to be in Python.
As yet we have no specification of the interface to the MCP server, and the establishment of that interface will enable a first level of evaluation of whether the intended services can efficiently be delivered as MCP servers.

The intention is that this will also be a testbed for the hosting facilities which would enable the services to be delivered in a scalable and efficient manner, with free and paid service levels.

## Prototype Driven Development Plan

There are many features of the intended system which will need to be prototyped as early as practical, and I envisage that development will be driven by the steps needed to evaluate as many of the highest risk innovations at the earliest possible stage as possible.

I will just mention some of the early steps beyond achieving MCP deployment of a minimal read capability.

- Update Capability
- Primitive Inference
- Independent development of metatheory
  Instead of tactics and tacticals this system will work with proven derived rules using reflexive features.
  Without the traditional machinery a repo of metatheory will have to be populated by transfer from another proof tool.
  It is only then that the primitive features for efficient computation and reflexion can be introduced.
- Deductive Intelligence
  In parallel with the development of the metatheoretic machinery enabling reflection, it will be possible to prototype the neural net heuristics for deductive intelligence.
- Choice of target languages for agentic verified software development.
