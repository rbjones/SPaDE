# The SPaDEroot Theory

The SPaDE root theory provides the foundational elements necessary for the formal specification of the SPaDE system. It includes the theory of T-expressions, which are tuple expressions and a minor elaboration of LISP S-expressions. This theory underpins the representation of abstract syntax and the structure of types and terms within SPaDE.

This theory forms a boundary between those parts of the SPaDE system specification which will be transferred materially unchanged into the core SPaDE native repository after first being developed and verified within the ProofPower environment.
It also represents a boundary beneath which may be found details of the implementation of features of space (such as the knowledge repository) which are not architectural or standardised and are not exposed on the MCP interface and are likely to be varied in diverse implementations of SPaDE repositories.
T-expressions appear not only in this specification, but also in the python interfaces between SPaDE subsystems and (represented in JSON) in the MCP protocol which is the primary means of delivering SPaDE capabilities to the LLMs which SPaDE is designed to serve.
They are therefore architectural, whereas the details of how the T-expressions consitituting a SPaDE repository are stored and manipulated may vary between different implementations, and it is intended that existing data structures such as SQL databases can be incorporated into an diasporic SPaDE repository using a suitable implementation of the knowledge repository interface.

This document is presented in the following parts:
- [Some SML Procedures](#some-sml-procedures) - to simplify the presentation of the SPaDE formal specifications.
- [Some HOL Constants](#some-hol-constants)
- [A Byte Sequence Packing Method](#the-byte-sequence-packing-method)
- [The Type oF T-expressions](#the-type-of-t-expressions)

All parts of this document are subject to further development as the needs of the SPaDE specifications evolve.

## Some SML Procedures

### SPaDE Theory Prelude

In this section a single procedure is defined to set up a theory prior to presenting its formal content.

```sml
fun force_new_theory name =
  let val _ = force_delete_theory name handle _ => ();
  in new_theory name
end;
```

```sml
fun new_SPaDE_theory (theory_name, parent, other_parents) =
    let val _ = open_theory parent;
        val _ = force_new_theory theory_name;
    in  map new_parent other_parents
end;
```

## Some HOL Constants

```sml
new_spade_theory ("SPaDEroot", "basic_hol", []);
```
## A Byte Sequence Packing Method

To introduce the type of T-expressions we must identify a representation for T-expressions over which the required operations are definable.

T-expressions are a free algebra generated from the empty set by an operator which takes a finite sequence of Bytes and a finite sequence of T-expressions.
Byte sequences will suffice as a representation if we can find an injection lists of byte sequences into byte sequences (since all the T-expressions supplied to the constructor are themsleves represented as byte sequences.

The required injection is obtained by convertin each byte sequence in the list into a null terminatedd byte sequence, using an escape character to handle any embedded nulls.
We might as well use the character X`01` as escape character.
Null is of course the byte X`00`.

In ProofPower HOL the type char represents a single byte (UNICODE characters are represented using utf8).
The type STRING is an abbreviation for LIST char.

In the following, pack_bytes must be an injection and unpack_bytes must be a left-inverse of pack_bytes.
In HOL it could be defined as a left inverse, but we want the functionality of SPaDE to be defined constructively so that it is potentially executable.

```sml
@HOLCONST
│   pack_bytes : LIST STRING -> STRING;
│   unpack_bytes : LIST STRING -> STRING;
├──────
│   True
■
```

## The Type of T-expressions