# Early KR prototyping

It is the (provisional) intention that the SPaDE project functionality will be delivered through one or more MCP servers and will be accessed by end-users via LLMs or later generations of AGI.

From the earliest possible stage we aim to have a prototype MCP server, delivering in the first instance some very elementary service, which will probably be low-level access to the content of SPaDE repositories.

I first intended to do this by scraping a ProofPower HOL repo to make a more or less equivalent SPaDE repository.
But while thinking this out, I decided that the import of theories from other systems (in general) important and non-trivial and the issues arising in the more general case are a distraction from putting together a quick and easy extract from ProofPower.
It also occurred to me that I could do a low level capability which would could create a repo from scratch, and this would suffice for a first prototype MCP server.

I am therefore considering a shorter route to exploring the exigencies of MCP servers by trying a simpler prototype which will create empty repositories and perform elementary operations to add and query material in them, probably at lower levels than the theory hierarchies which will ultimately populate them.

All of this either is or will be more fully documented in other documents but for the purposes of the very first prototype I note that the more elaborate structure of a theory heirarchy is represented in SPaDE using a simple representation essentially the same as LISP S-expressions, which in turn is linearised as a sequence of null-terminated UTF-8 strings.
The first very firstrepo can offer low level facilities for reading and writing such files, and for creating a repo from scratch, and need not have any knowledge or facilities specific to the intended application of the structures.

## An Overview of the Repository Prototyping Strategy

The intention is that a repository is an abstract structure which will be linearised for storage in a simple file for the SPaDE native repository structure.
It is not thought that the extra complications involved in the use of more sophisticated database software will have significant benefits (though this will be reviewed as prototyping progresses).

The repository will be accessed in the first instance by the KR subsystem, which will read the linear representation and create a structured representation more convenient for the intended usage.
The first level of use of this will be by the deductive "kernel" (DK) which will provide a first layer of inferential capability.
The second level of use, making use of the deductive kernel will involve focal AI, along the lines of DeepMind's alpha-zero, using neural net heuristics to guide Monte Carlo Tree Search (MCTS) processes.
This differs from a typical application of that approach because we will be treated each context as a separate "perfect information space" with its own neural net, resulting in a hierarchy of intelligent agents which collaborate in the solution of any problem.

The resulting capabilities will then made available through an MCP server interface.

In the first instance, neither intelligent nor even deductive capabilities will be provided, but we will nevertheless approach as early as possible the delivery of some service through an MCP server.
That earliest service will be simply access to the content of a theory hierarchy, and to provide that service we will export theory hierarchies from existing HOL ITP systems.

### The first prototype

The first prototype will be a simple MCP server which can create an empty repository or open an existing repository as an S-expression.
It will support the primitive operations on S-expressions and allow extention of the repository by appending new S-expressions built using the existing structures, new atoms and CONS cells.

## [The Structure of a SPaDE repository](SPaDENativeRepo.md)

A SPaDE repository contains a heirarchy of contexts or theories, each of which introduces various names by including them in a signature indicating what type of value they denote, and providing a constraint which assigns meaning to the names.
At the lowest level, to provide complete generality, these structures are stored in a postfix format in which both operands and operators are represented as null-terminated UTF-8 strings.
This is further simplified by the structural device which we see in LISP in which aribitrary structures are represented in an underlying structure with only one constructor (CONS).

## The Linearisation of Structured Repositories

Since we are representing the more elaborate structure of a theory heirarchy using structures essentially the same as LISP S-expressions the problem of linearising these for storage in a simple file format becomes a matter of defining a clear mapping between S-expressions and a flat representation.
We can therefore write the software to perform this mapping, before we determine the details of how the theory hierarchy is mapped into S-expressions.

In the first instance we need to write in SML software for writing such a repository, and in Python (main candidate for implementation of the SPaDE MCP server) we need to be able to read this format (in the first instance, and later to append extra structure to the files, which will also cover creating from scratch and is the only kind of write access anticipated).

So we need to have a python procedure (or method?) which writes such a list structure into a file in a postfix format, and one for reading such a file and reconstructing the structure.  The atoms will all be null terminated utf8 character strings, NIL will be the empty string, and there will be only the one operator.  In order to admit the inclusion of null bytes in these "strings" (so that they become arbitrary byte sequences), the "\\" character will be used as an escape.  The postfix linear format to be written to the file, will consist exclusively of a series of null terminated utf8 strings, of which the first character identifies the string as CONS if it consists only of the character 0, and will otherwise begin with the character "1" followed by the string (or empty string) representing a operand.   To convert the linear file into a list structure, use a stack, the elements of which are either atoms or links to lists already formd, push atoms onto the stack until a CONS is reached, then perform a CONS on the top two elements, which are then removed and replaced by a link to the CONS cell.   Before approaching this problem, consider carefully whether you have understood this description, and ask for clarification if you have any doubts.
