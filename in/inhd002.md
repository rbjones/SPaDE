# Generic Abstract Syntax Support for EBNF Grammars

# Introduction

Multiple routes to generic support for abstract syntax are under consideration for use in SPaDE metatheory and knowledge onboarding.
This document concerns the use of EBNF grammars to provide generic support for abstract syntax in SPaDE.

The first step is to enable grammers expressed in EBNF to be interpreted and processed in a generic manner within SPaDE, by translating those grammers into T-expressions, and implementing generic facilities supporting the notations thus represented.

## EBNF Grammar Syntax

The following presents the syntax of EBNF grammars in EBNF itself.
It was done by Gemini (not quite right!), and then adjusted by RBJ.
As of the present there are still problems in it (no account of the "{","}" repetition notation in EBNF).
It's an exploration, and though ebnf will be used informally, a more formal role is sub-judice.

```ebnf
(* The root production of an EBNF grammar *)
syntax          = { syntax rule } ;

(* A single rule definition *)
syntax rule     = meta identifier , "=" , definitions list , ";" ;

(* Alternatives separated by vertical bars or slashes *)
definitions list= single definition , {"|" , single definition} ;

(* A sequence of terms *)
single definition= syntactic term , { "," , syntactic term } ;

(* A term with an optional quantitative multiplier *)
syntactic term  = [ integer , "*" ] , syntactic factor ;

(* Factors include primaries, exceptions, options, or repetitions *)
syntactic factor= syntactic primary 
                | exception 
                | repetition 
                | optional 
                | group ;

(* The basic building blocks *)
syntactic primary= meta identifier 
                | terminal string 
                | empty 
                | special sequence ;

(* Modifiers and groupings *)
exception       = syntactic primary , "-" , syntactic factor ;
repetition      = integer , "*" , syntactic primary ;
optional        = "[" , definitions list , "]" ;
group           = "(" , definitions list , ")" ;

(* Terminals and identifiers *)
meta identifier = letter , { letter | decimal digit } ;
integer         = decimal digit , { decimal digit } ;
terminal string = "'" , { character } , "'" 
                | '"' , { character } , '"' ;
special sequence= "?" , { character } , "?" ;
empty           = ;
```


