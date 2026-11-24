"""Tests for the translation of ASN.1 modules into HOL T-expressions.

Author: Grok Build (Grok 4.7)
"""

import pytest

from incd001 import ParseError, translate


PAIR = """
Demo DEFINITIONS ::= BEGIN
    Pair ::= SEQUENCE { left INTEGER, right INTEGER }
END
"""

RICH = """
Demo DEFINITIONS AUTOMATIC TAGS ::= BEGIN
    -- a comment
    Tree ::= CHOICE {
        leaf [0] IMPLICIT INTEGER (0..MAX),
        branch SEQUENCE {
            left Tree OPTIONAL,
            right Tree DEFAULT leaf : 0,
            ...
        }
    }
    answer INTEGER ::= 42
END
"""


def test_pair_module_uses_the_t_constructor():
    assert translate(PAIR) == """\
T ("module", [
    T ("name", [
        T ("Demo", [])
    ]);
    T ("objectIdentifier", []);
    T ("untagged", []);
    T ("body", [
        T ("typeAssignment", [
            T ("name", [
                T ("Pair", [])
            ]);
            T ("sequence", [
                T ("component", [
                    T ("name", [
                        T ("left", [])
                    ]);
                    T ("integer", []);
                    T ("required", [])
                ]);
                T ("component", [
                    T ("name", [
                        T ("right", [])
                    ]);
                    T ("integer", []);
                    T ("required", [])
                ])
            ])
        ])
    ])
])"""


def test_comments_tags_constraints_and_values_are_kept():
    term = translate(RICH)
    assert 'T ("automatic", [])' in term
    assert 'T ("tagged", [' in term
    assert 'T ("implicit", [])' in term
    assert 'T ("constrained", [' in term
    assert 'T ("(0..MAX)", [])' in term
    assert 'T ("optional", [])' in term
    assert 'T ("default", [' in term
    assert 'T ("constructed", [' in term
    assert 'T ("extension", [])' in term
    assert 'T ("integerValue", [' in term
    assert 'T ("42", [])' in term
    assert "comment" not in term


def test_several_modules_are_separate_terms():
    source = PAIR + "\nOther DEFINITIONS ::= BEGIN\n    Flag ::= BOOLEAN\nEND\n"
    first, second = translate(source).split("\n\n")
    assert first.startswith('T ("module", [')
    assert 'T ("Other", [])' in second
    assert 'T ("boolean", [])' in second


def test_a_quotation_mark_in_a_literal_is_a_character_code():
    source = '''
Demo DEFINITIONS ::= BEGIN
    greeting IA5String ::= "say ""hi"""
END
'''
    term = translate(source)
    assert '("say " @ [`\\034`] @ "hi" @ [`\\034`])' in term


def test_a_rejected_construct_names_its_location():
    source = "Demo DEFINITIONS ::= BEGIN\n    Pair { } ::= INTEGER\nEND\n"
    with pytest.raises(ParseError, match=r"line 2, column 10"):
        translate(source)
