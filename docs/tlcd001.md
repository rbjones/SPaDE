# SPaDE formal specification - Overview and Abstract Syntax

## Introduction

This is the first of a series of documents intended to provide formal specifications for the SPaDE system, in particular for the representation of knowledge in SPaDE.

It is written in ProofPower HOL to enable its checking and use to be undertaken in advance of support for HOL in SPaDE, with the intention that it will in due course be ported into SPaDE itself and support reasoning by SPaDE about itself at all levels.

The initial versions developed in HOL will be worked in the context of a fairly well-populated ProofPower HOL database.
In order to port this into a SPaDE repository it will be necessary to minimise the context, but for the purpose of guiding the implementation of early versions of the knowledge repository, tha minimisation will not be needed and would only complicate the initial development.

In relation to those primitive theories, the main thrust of the changes is to place front and center reflexive reasoning about SPaDE itself, rather than, say formalising the real numbers.
Intended strengthening of the axiom of infinity will only be relevant to underpinning the claim to universality of the foundational institution  (see tlph010.md).

The entire structure of SPaDE respository is considered here as *abstract syntax* represented as T-expressions, so that a SPaDE repository, and hence every non-trivial part of it, is a T-expression.
Apart from T-expressions, the only other constituents of T-expressions are byte sequences, which serve to identify the syntactic category and the particular constructor for that variant of the category.
This, application of the byte sequence, and also its use as a literal, involve packing multiple byte sequences together to form the complete representation.

The proposed implementation of the knowledge repository will be syntactically generic, and so this document begins by identifying a very simple representation for grammars as T-expressions and then defines the abstract syntactic structure of a SPaDE repository.

The abstract syntax will be given by identifying the syntactic categories for each structure in the SPaDE repository, and the constructors for each category, together with the arity of the constructors, which form a tuple of syntactic categories.
This information will be coded as a T-expression, so that much of the functionality of SPaDE can be implmented in a concise table driven manner.

- [The Representation of Abstract Syntax](#the-representation-of-abstract-syntax)
- [Scalar Data Forms](#scalar-data-forms)
- [Syntactic Categories](#syntactic-categories)
- [Syntactic Constructors](#syntactic-constructors)
- [Name Spaces and Contexts](#name-spaces-and-contexts)
- [Well-formedness Conditions](#well-formedness-conditions)

```sml
new_SPaDE_theory ("tlcd001", "T_ex", []);
force_new_pc "'tlcd001";
set_pc "SPaDEroot";
```

### The Representation of Abstract Syntax Grammars

This section presents a grammer for grammers as a T-expression together with a semantics for this notation which determines which T-expressions comply with any grammer expessed in that way.

The grammar for grammars will serve as a meta-level specification, guiding the construction and interpretation of T-expressions that represent the abstract syntax of SPaDE repositories.

These grammars are partial accounts of the structure since two aspects of potential structure are not captured (and in application to SPaDE, are not essential to the integrity of the deductive system).
These represent points at which we dip into literal substructure of the kind one obtained by quoting a T-expression rather than using it.
These can be given meaning by applying to them some semantic function, but this would be part of an application of SPaDE rather than part of the HOL logic itself.

Informally the grammars we consider have the following structure.

1. A set of syntactic categories, each representing a distinct kind of syntactic entity.
2. For each syntactic category, a set of constructors that can be used to build instances of that category.
3. For each constructor, an arity specifying the number and types of its arguments, which are themselves syntactic categories.
4. Lists are permitted both in the the arity and in the result category.
5. "T_ex" is a built in syntactic category representing T-expressions themselves, and which place no additional constraint on the T-expression which appears at that point.

In using T-expressions to capture such a grammar, and in the required structure determined by the grammer, the byte sequence which begins a T-expression representing a phrase consists of one byte for the syntatic category and one for the particular constructor being used.
In the case of an atomic T-expression, the byte sequence may either have that same form, or it may begin with the code for a literal and its form them depends upon coding conventions not specified here.

```
grammar = category list
category = constructor list
constructor = item list
item = category_no | list_of syntactic_category
syntactic_category = "T_ex" | identifier
```

### T-Expressions as a Representation for Abstract Syntax

The idea that T-expressions are a natural way to represent abstract syntax came to me, I now see, through too exclusive a focus on the ways in which syntactic structures are manipulated in LCF-style proof assistants.
Nevertheless, that is the business at hand and they will suffice for the abstract syntax of the SPaDE repository.

The representation of SPaDE abstract syntax by T-expressions will take place at two levels.
Ground level and meta-level.

At the ground level, the T-expressions represent the actual syntactic entities of the SPaDE repository, with their constituents and structure directly encoded.
At the meta-level, the T-expressions are used to describe the abstract syntax of the SPaDE repository, and thus represent primarily the grammar of the syntax of SPaDE repositories.
This grammar is then to be used to define the various operations which the SPaDE kr substem performs on SPaDE repositories.
The T-expressions encoding that grammar will be formally defined here in ProofPower HOL, and later transcribed into SPaDE repositories to support the metatheoretic aspects of RSI in SPaDE.

Having chosen T-expressions as a generic representation aligned to that kind of system, the idea that generic facilities could be built on it which are triggered by translating a more conventional concrete description of abstract syntax, such as BNF and its variants, seemed natural.
But having looked at some examples and puzzled how to make this work, I have come down against it, while still thinking that a generic implementation of much of the handling of the SPaDE repository (regarded as abstract syntax) may nevertheless be feasible and worthwhile.

So I am now attempting an approach to genericism which is oriented to achieving generality by representing the constructors for syntactic entities as T-expressions.
This will be particularly rudimentary because the abstract syntax of the SPaDE repository is simple, and so more elaborate constructions which might be desirable for the representation of more elaborate abstract syntax will not be necessary here, but could possibly be added later if support were later found to be desirable.

In representing structures using T-expressions there are three kinds of structure which can be introduced:

- The use of T-expressions for constructors
        The scalar field then identifies the syntactic category and the particular construction, and the constituent expressions are represented by the constituent T-expressions.
- The use of T-expressions for operators on constituents
        A constituent in a construction rule may be modified by allowing a list, or allowing alternatives.  It is not clear whether we need to support these for SPaDE
- Where there are no subsidiary expressions, we may pack within the scalar field data in addition to the syntactic category and constructor identification.  The category and constructor will then determine the interpretation of the remaining data.

It is implicit in this approach that the scalar field of the T-expression is used to pack up multiple components, and will therefore be routinely unpacked when being processed, unless the necessary discrimination can be made directly from the packed representation.


But there is also the possibility of adding structure within the scalar which is the content of a 0-ary T-expression, a byte sequence in which we may encode a sequence of byte sequences, allowing that such encodings can themselves carry structured information.
This kind of substructure will be used in the first instance to include in the constructor identification both the syntactic category and the particular constructor for that variant of the category.
Some syntactic categories may then, instead of having detail in a sequence of T-expressions, have less elaborate information coded directly as additional subelements of the scalar byte sequence of the 0-ary T-expression.

Thus, to secure efficiency in the processing of the relativised pathnames which distinguish all SPaDE HOL constants, such a relativised path will be a 0-ary T-expression in which the scalar byte sequence encodes the sequence of components of the path together with the relative height of the starting point for the path.
When working in a normalised context, constant comparisons can then be undertaken without unpacking the resulting byte sequence.

An important issue in this is the representation of names as relative paths within the T-expressions, since comparison of names occurs frequently and needs to be efficient.
The present solution is to pack the components of a relative path into the scalar byte sequence of a 0-ary T-expression, encoding both the sequence of components and the relative height of the starting point for the path.
It may be noted that under the hood the low level implementation of T-expressions as NTBSS involves the use of pointers to constituent byte sequences, and the caching of the targets, so that no two distinct pointers refer to the same NTBS, and enabling equality checks to avoid following the link.

Once we get off ground level, the syntactic constructors are all represented as T-expressions in which the initial byte sequence is an NTBSS coding both the syntactic category and the particular constructor for that variant of the category.
This is part of a systematic attempt to make all the structures self-identifying as to their syntactic category.

At the ground level (as far as the T-expressions hierarchy is concerned), we have T-expressions with empty lists of subexpressions, in which case various kinds of data may be directly encoded in the byte sequence after the category indicator.


These include *names*, *paths* and various kinds of *literals*.

## The Abstract Syntax of SPaDE

### BNF

```
Sname = BS
Rname = ℕ , Sname LIST
Type =      Tyvar SName
        |   Tcon Rname, Type LIST
Term =      Var Sname, Type
        |   App Term, Term
        |   Lam Sname, Type, Term
Ext =       Tydef Sname, ℕ, Term
        │   Tmdef Sname, Type, Term
Folder =    
Taglist * =   TList Taglist, Tag, *

```


### Packing Scalars

In the majority of cases the scalar field of a T-expression will be used to encode multiple components, such as the syntactic category, the particular constructor, and any additional data required for the interpretation of the T-expression.

The following function facilitates the packing of such fields.

```sml
ⓈHOLCONST
│   packScalar: ℕ LIST → BS
├─
│   packScalar = Map AbsChar
■
declare_alias("P", ⌜packScalar⌝);

```

### Scalar Data Forms

Scalar data in T-expressions is located as the first byte sequence of every T-expression.
When the T-expression represents a constructor in the abstract syntax the information held in that byte sequence will identify the syntactic category of the result, and the particular manner of construction, which together will determine the number and kinds of the subexpressions (*T-exp*s) that follow.

For T-expressions that represent scalar data rather than constructors, the byte sequence directly encodes the value of the scalar, such as a name, path, or literal.
The distinction between constructors and scalars thus enunciated cannot be determined by the presence or absence of subexpressions alone, since it is not uncommon to have syntactic constructors which have no subexpressions.
It is therefore to be encoded in the initial byte sequence of the T-expression.

Though it is not essential, it is proposed to make all use of T-expression in the SPaDE repository self-identifying through the initial byte sequence, and this includes the particular structures which are coded into the scalar byte sequence of the T-expression, and excludes only certain points in the repository at which T-expressions are made available for purposes opaque to the SPaDE system.

### Syntactic Categories

We simply enumerate the categories here and assign numeric values to them.

```sml
ⓈHOLCONST
│   ScalarC SnameC RnameC TypeC TermC ExtC
│   ThryC FoldC CommC: ℕ
├────────────
│   ScalarC = 7
│∧  SnameC = 8
│∧  RnameC = 9
│∧  TypeC = 10
│∧  TermC = 11
│∧  ExtC = 12
│∧  ThryC = 13
│∧  FoldC = 14
│∧  CommC = 15
■
```

### Syntactic Constructors

The constructors have more elaborate data.
For each syntactic category, the constructors are enumerated and assigned numeric values, similar to the categories themselves.
In addition, the arity of the construction is specified, indicating the number of subexpressions that the constructor takes and the category of each subexpression.

Still issues to resolve on the representation of names and paths.
We'll come back to that, and test out on the more straightforward consturctors.
One T_ex per rule.




```
ⓈHOLCONST
│   : T_ex
├────────────
│   
■
```

### Name Spaces and Contexts

### Well-formedness Conditions

```
ⓈHOLCONST
│   name: T_ex;
│   sname: T_ex;
│   rname: T_ex;
├──────
│   name = mk_NTBSS ("sname",[])
│∧  sname = mk_NTBSS ("rname",[])
■
```