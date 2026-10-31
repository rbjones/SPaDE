# Proposal: Structured Project Data for SPaDE Repositories

## Purpose

This proposal is to make structured parts of SPaDE project documentation, especially task descriptions and their relationships, suitable for transfer into a SPaDE-native repository.

The proposed approach is to author structured data in a restricted YAML profile, validate it against JSON Schema, and define an explicit mapping from its data model to T-expressions. YAML would be a human-readable concrete syntax; the T-expression structure would be the transferable representation. This proposal does not require existing Markdown documents to be replaced or migrated now.

The proposal supports the objective in [amms001.md](amms001.md) of making project descriptions available as declarative knowledge in SPaDE repositories. T-expressions are specified in [tlcd004.md](../tlcd004.md).

## Proposed scope

Begin with structured records for tasks: identifiers, titles, status, inputs, outputs, constraints, and dependencies. Keep explanatory prose in Markdown unless and until a separate representation is justified. A structured record may accompany a task description without changing the existing document hierarchy or workflow.

The same data model could later be used for other project records, such as requirements and decisions. Those uses would need their own schemas and conventions.

## Possible HOL integration

A future way to work with these records in HOL would be to provide a generic parser and pretty-printer, parameterized by a record's schema. Given the schema, the parser would map YAML records to `T_ex` terms, and the pretty-printer would render such terms as YAML of the corresponding shape.

This is a possible direction, not part of the present proposal's implementation scope. For now, authoring and validating the YAML records is sufficient; the example T-expression renditions below illustrate the intended relationship without requiring a HOL parser or printer.

## YAML profile

Use YAML 1.2 with its JSON schema for resolving plain scalars, restricted to values that can be represented as JSON data:

- mappings with string keys, sequences, strings, JSON numbers, booleans, and null;
- a single document per record;
- no duplicate mapping keys, aliases, anchors, merge keys, custom tags, or complex mapping keys;
- quote strings that would otherwise resolve as a number, boolean, or null.

This restriction avoids YAML features that do not map directly to the JSON data model. It also avoids relying on version-dependent implicit typing. A conforming parser must reject duplicate keys rather than silently choose one.

## Validation

Use JSON Schema to describe the permitted structure and constraints of each record type. Choose and declare a JSON Schema dialect for each schema. Validate the data model produced by the YAML parser, not YAML syntax directly.

JSON Schema describes record shape and value constraints; it does not define the YAML profile or the mapping to T-expressions. These are separate parts of the proposal.

## Mapping to T-expressions

Define the mapping on the parsed data model, independently of YAML presentation details. A simple generic mapping is:

| Data value | T-expression form |
| --- | --- |
| Mapping | `mapping` with one `entry` child for each key/value pair |
| Entry | `entry` with a `string` key child and a value child |
| Sequence | `sequence` with one child per item, in sequence order |
| String | `string` whose byte sequence is the string's UTF-8 encoding |
| Number | `number` with a representation defined by the profile |
| Boolean | `true` or `false` nullary constructor |
| Null | `null` nullary constructor |

These constructor names are illustrative. The mapping specification must settle their exact byte names and child order before it is used as an interchange contract.

T-expression children are ordered, but YAML mappings have no semantic order. Therefore, encode mapping entries in ascending order of the UTF-8 bytes of their keys. Preserve sequence order. This makes the T-expression tree independent of the order in which mapping keys happen to appear in a YAML file.

The representation of numbers needs an explicit rule. It must preserve JSON number meaning and make clear whether equivalent spellings such as `1` and `1.0` map to the same T-expression. This proposal leaves that rule open for a small implementation trial.

## Example

```yaml
id: tltd-example
title: Example task
status: proposed
inputs:
  - issue
  - repository
outputs:
  - reviewable change
constraints:
  - no schema changes
depends_on: []
```

The following JSON Schema (Draft 2020-12) requires these fields and constrains their types. It accepts the example and other task records with the same shape. Its parsed mapping would map to a T-expression tree using the rules above; the exact tree serialization is not implied by the YAML layout.

```json
{
  "$schema": "https://json-schema.org/draft/2020-12/schema",
  "title": "SPaDE task record",
  "type": "object",
  "properties": {
    "id": {
      "type": "string",
      "minLength": 1
    },
    "title": {
      "type": "string",
      "minLength": 1
    },
    "status": {
      "type": "string",
      "minLength": 1
    },
    "inputs": {
      "type": "array",
      "items": {
        "type": "string"
      }
    },
    "outputs": {
      "type": "array",
      "items": {
        "type": "string"
      }
    },
    "constraints": {
      "type": "array",
      "items": {
        "type": "string"
      }
    },
    "depends_on": {
      "type": "array",
      "items": {
        "type": "string",
        "minLength": 1
      },
      "uniqueItems": true
    }
  },
  "required": [
    "id",
    "title",
    "status",
    "inputs",
    "outputs",
    "constraints",
    "depends_on"
  ],
  "additionalProperties": false
}
```

## Generic ProofPower HOL rendition

One generic encoding of the parsed YAML data model is a term of type `T_ex`, using the alias `T` for `mk_T_ex` declared in [tlcd004.md](../tlcd004.md). Here each mapping entry is an `entry` with a `string` key and a value; each sequence is a `sequence`. A string value is represented by a `string` node whose child is a leaf labelled by the string's UTF-8 bytes. Mapping entries are ordered by key as specified above.

```hol
T ("mapping", [
  T ("entry", [
    T ("string", [T ("constraints", [])]),
    T ("sequence", [
      T ("string", [T ("no schema changes", [])])
    ])
  ]),
  T ("entry", [
    T ("string", [T ("depends_on", [])]),
    T ("sequence", [])
  ]),
  T ("entry", [
    T ("string", [T ("id", [])]),
    T ("string", [T ("tltd-example", [])])
  ]),
  T ("entry", [
    T ("string", [T ("inputs", [])]),
    T ("sequence", [
      T ("string", [T ("issue", [])]),
      T ("string", [T ("repository", [])])
    ])
  ]),
  T ("entry", [
    T ("string", [T ("outputs", [])]),
    T ("sequence", [
      T ("string", [T ("reviewable change", [])])
    ])
  ]),
  T ("entry", [
    T ("string", [T ("status", [])]),
    T ("string", [T ("proposed", [])])
  ]),
  T ("entry", [
    T ("string", [T ("title", [])]),
    T ("string", [T ("Example task", [])])
  ])
])
```

## T-expressional rendition of the YAML example

The same task record can instead be expressed directly as abstract syntax: the root constructor is `task`; each field name is a constructor; and its child or children encode the field value. For string-valued fields, a single child holds the string. For sequence-valued fields, the children hold the items in order; an empty sequence therefore has no children. The constructor names shown here are illustrative, and their byte encodings are the UTF-8 encodings of the displayed names.

```sml
⌜T ("task", [
  T ("id", [
    T ("tltd-example", [])
  ]),
  T ("title", [
    T ("Example task", [])
  ]),
  T ("status", [
    T ("proposed", [])
  ]),
  T ("inputs", [
    T ("issue", []),
    T ("repository", [])
  ]),
  T ("outputs", [
    T ("reviewable change", [])
  ]),
  T ("constraints", [
    T ("no schema changes", [])
  ]),
  T ("depends_on", [])
])
```

## Migration and evaluation

Before adopting this approach project-wide:

1. Define a schema for one representative task record.
2. Implement parsing, profile checks, JSON Schema validation, and mapping to T-expressions.
3. Test that permitted YAML variations produce the same data model and T-expression, especially variation in mapping-key order.
4. Record the chosen number representation and constructor names.
5. Evaluate whether structured task records help retrieval and continuation of work in a SPaDE repository while retaining Markdown as the human-readable explanation.

Adoption should follow only if the trial demonstrates a useful, stable correspondence. Until then, this document is a proposal, not a required documentation format.
