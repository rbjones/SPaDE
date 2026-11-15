# Generic Abstract Syntax

The title is provisional. This document is to give the generic account of an abstract syntax: the syntactic categories of a notation and the rules by which phrases of those categories are formed. It begins with the notation in which that account is written, described in itself.

The notation is Abstract Syntax Notation One (ASN.1), specified by ISO/IEC 8824-1:2021, the text of which is identical with ITU-T X.680 (02/2021). That standard defines a notation for data types, for values of those types, and for constraints on types. The encoding rules are a separate standard, ISO/IEC 8825, and form no part of the notation described here.

An abstract syntax, as fixed in [tlph010.md](tlph010.md), is a set of syntactic categories together with rules for forming an object of one category from objects of other categories. In ASN.1 the corresponding word is *type*. A type of this notation is read here as a syntactic category, or as an expression that builds one. A module is the notation's collection of such definitions.

## The notation in itself

The following module is an abstract syntax for the fragment of ASN.1 used to write an abstract syntax. It is written in that fragment. The standard remains the definition of the full notation. Tags, optional and default components, unordered collections, constraints, and information objects belong to that full notation and are omitted here.

```asn1
ASN1-Notation DEFINITIONS AUTOMATIC TAGS ::= BEGIN

Module ::= SEQUENCE {
    name        ModuleName,
    assignments SEQUENCE OF Assignment
}

ModuleName ::= UTF8String

Assignment ::= CHOICE {
    typeAssignment  SEQUENCE {
        name TypeName,
        type Type
    },
    valueAssignment SEQUENCE {
        name  ValueName,
        type  Type,
        value Value
    }
}

TypeName  ::= UTF8String
ValueName ::= UTF8String

Type ::= CHOICE {
    named        TypeName,
    boolean      NULL,
    integer      NULL,
    octetString  NULL,
    utf8String   NULL,
    null         NULL,
    choice       SEQUENCE OF Alternative,
    sequence     SEQUENCE OF Component,
    sequenceOf   Type
}

Alternative ::= SEQUENCE {
    constructor Identifier,
    type        Type
}

Component ::= SEQUENCE {
    name Identifier,
    type Type
}

Identifier ::= UTF8String

Value ::= CHOICE {
    boolean      BOOLEAN,
    integer      INTEGER,
    octetString  OCTET STRING,
    utf8String   UTF8String,
    null         NULL,
    constructed  SEQUENCE {
        constructor Identifier,
        arguments   SEQUENCE OF Value
    },
    sequence     SEQUENCE OF NamedValue,
    sequenceOf   SEQUENCE OF Value
}

NamedValue ::= SEQUENCE {
    name  Identifier,
    value Value
}

END
```

A `Module` is a name and a list of assignments. A `typeAssignment` names a syntactic category and gives the type expression which defines it. A `valueAssignment` names a phrase, states its category, and gives the phrase.

A `Type` is a type expression:

- `named` refers to a category by name.
- `boolean`, `integer`, `octetString`, `utf8String`, and `null` are primitive categories. Each is a constructor of a type expression with no argument. Their phrases are the booleans, the integers, the octet strings, the UTF-8 strings, and the single empty phrase.
- `choice` is a list of alternatives. Each alternative is one constructor, named by an identifier, with one argument type.
- `sequence` is a list of named components, and is the argument list of a single constructor.
- `sequenceOf` is the category of finite lists of phrases of one type.

A `Value` is a phrase. `constructed` is a constructor applied to its argument phrases, and is a phrase of a choice. `sequence` is a list of named component phrases. `sequenceOf` is a list of phrases. The primitive alternatives are phrases of the primitive categories. The `NULL` which appears as the argument of `integer` in a type expression is the empty argument of that constructor of type expressions. It is a different phrase from an integer.

In the written notation a type name begins with an uppercase letter and an identifier with a lowercase letter. A type assignment is written `Name ::= Type`. The constructors of a type expression are written `BOOLEAN`, `INTEGER`, `OCTET STRING`, `UTF8String`, `NULL`, `CHOICE { constructor Type, ... }`, `SEQUENCE { name Type, ... }`, and `SEQUENCE OF Type`. A phrase of a choice is written `constructor : value`. A phrase of a sequence is written `{ name value, ... }`. A list is written `{ value, ... }`.

The written assignment

```asn1
Pair ::= SEQUENCE { left INTEGER, right INTEGER }
```

is this phrase of category `Assignment`:

```asn1
typeAssignment : {
    name "Pair",
    type sequence : {
        { name "left",  type integer : NULL },
        { name "right", type integer : NULL }
    }
}
```

`AUTOMATIC TAGS` directs an encoding in distinguishing the alternatives of each choice. The tags are not constructors. `OPTIONAL`, `DEFAULT`, `SET`, `SET OF`, and constraints further restrict or vary the phrases of a type. They are formation beyond the free algebra of this fragment, and they remain available in the standard when a notation needs them.

The generic abstract syntax is to be written in this fragment.

---

Document ID: tlad016
Author: Grok Build (Grok 4.7)
