"""Translate an ASN.1 module into a ProofPower HOL term built with T.

Author: Grok Build (Grok 4.7)

T is the alias of mk_T_ex declared in docs/tlcd004.md. Its type is
BS × T_ex LIST → T_ex. A phrase is written

    T ("label", [child; child])

and a childless phrase is written T ("label", []). The term is the
abstract syntax of the module, for use as the object of a semantic
definition in HOL. It is not an encoding of values under BER or PER.

A spelling (a name, a number, or the text of a literal or a constraint)
is the label of a childless phrase, and that phrase occurs only as the
child of name, number, or literal. Every other label is a constructor.
A brace of named values is sequenceValue. A brace of unnamed values is
sequenceOfValue. An empty brace is sequenceValue.

    T ("name", [T ("Pair", [])])
    T ("number", [T ("42", [])])
    T ("literal", [T ("0A0B", [])])

The module phrase has four children, in this order: its name, its object
identifier (childless when the module writes none), its tag default
(automatic, explicit, implicit, or untagged), and its body. The body
holds the assignments, exports, and imports in source order.

A component has three children: its name, or anonymous; its type; and
required, optional, or default. A default carries the omitted value.
A choice alternative has two children: its name, and its type.

Tags, OPTIONAL, DEFAULT, SET, and a parenthesised constraint are kept,
because they are written in the concrete syntax. A constraint is kept
as its source text, including the parentheses, rather than as a further
syntax.

The concrete syntax accepted is the module notation of X.680 used to
define an abstract syntax: type and value assignments, the usual
primitive types, CHOICE, SEQUENCE, SET, SEQUENCE OF, SET OF, ENUMERATED,
named numbers, tags, constraints, extension markers, COMPONENTS OF,
EXPORTS, and IMPORTS. Parameterised types and information-object classes
are rejected with a located error.

Usage: python3 in/incd001.py module.asn …
With no file argument, the module is read from the standard input.
One module produces one term. Several modules in one file produce one
term after another, separated by a blank line.
"""

from __future__ import annotations

import sys
from dataclasses import dataclass


class ParseError(Exception):
    """The concrete syntax is outside the accepted notation."""


@dataclass(frozen=True)
class Token:
    kind: str
    value: str
    start: int
    end: int


Node = tuple


def translate(source: str) -> str:
    """Return the HOL term or terms for the modules written in source."""
    parser = Parser(source)
    modules = parser.parse_modules()
    return "\n\n".join(render(module) for module in modules)


def hol_literal(text: str) -> str:
    """A ProofPower string or character-list term denoting text."""
    if all(_plain_character(character) for character in text):
        return '"' + text + '"'
    parts: list[str] = []
    buffer: list[str] = []

    def flush() -> None:
        if buffer:
            parts.append('"' + "".join(buffer) + '"')
            buffer.clear()

    for character in text:
        if _plain_character(character):
            buffer.append(character)
            continue
        flush()
        parts.append(character_term(character))
    flush()
    if not parts:
        return '""'
    return parts[0] if len(parts) == 1 else "(" + " @ ".join(parts) + ")"


def _plain_character(character: str) -> bool:
    code = ord(character)
    return character not in '"\\`' and (code >= 128 or 32 <= code < 127)


def character_term(character: str) -> str:
    """A one-character CHAR LIST. The code is a ProofPower character literal."""
    code = ord(character)
    if code > 255:
        return '"' + character + '"'
    return "[`\\%03d`]" % code


def render(node: Node, indent: int = 0) -> str:
    label, children = node
    shown = hol_literal(label)
    if not children:
        return f"T ({shown}, [])"
    pad = "    " * indent
    inner = "    " * (indent + 1)
    body = (";\n" + inner).join(render(child, indent + 1) for child in children)
    return f"T ({shown}, [\n{inner}{body}\n{pad}])"


def leaf(label: str) -> Node:
    return (label, [])


def name(spelling: str) -> Node:
    return ("name", [leaf(spelling)])


def number(spelling: str) -> Node:
    return ("number", [leaf(spelling)])


def literal(spelling: str) -> Node:
    return ("literal", [leaf(spelling)])


class Parser:
    def __init__(self, source: str) -> None:
        self.source = source
        self.tokens = tokenize(source)
        self.index = 0

    def parse_modules(self) -> list[Node]:
        if self.peek().kind == "eof":
            self.fail("a module is required")
        modules = []
        while self.peek().kind != "eof":
            modules.append(self.parse_module())
        return modules

    def parse_module(self) -> Node:
        module_name = self.expect_type_name()
        if self.at("{", "sym"):
            identifier = ("objectIdentifier", [literal(self.balanced("{", "}"))])
        else:
            identifier = ("objectIdentifier", [])
        self.expect_word("DEFINITIONS")
        default = leaf("untagged")
        if self.at_word("AUTOMATIC"):
            self.expect_word("AUTOMATIC")
            self.expect_word("TAGS")
            default = leaf("automatic")
        elif self.at_word("EXPLICIT"):
            self.expect_word("EXPLICIT")
            self.expect_word("TAGS")
            default = leaf("explicit")
        elif self.at_word("IMPLICIT"):
            self.expect_word("IMPLICIT")
            self.expect_word("TAGS")
            default = leaf("implicit")
        self.expect_symbol("::=")
        self.expect_word("BEGIN")
        items: list[Node] = []
        while not self.at_word("END"):
            if self.at_word("EXPORTS"):
                items.append(self.parse_exports())
            elif self.at_word("IMPORTS"):
                items.append(self.parse_imports())
            else:
                items.append(self.parse_assignment())
                if self.at(";", "sym"):
                    self.advance()
        self.expect_word("END")
        return ("module", [name(module_name), identifier, default, ("body", items)])

    def parse_exports(self) -> Node:
        self.expect_word("EXPORTS")
        if self.at_word("ALL"):
            self.advance()
            exported: list[Node] = [leaf("all")]
        else:
            exported = []
            if not self.at(";", "sym"):
                exported.append(name(self.expect_reference()))
                while self.at(",", "sym"):
                    self.advance()
                    exported.append(name(self.expect_reference()))
        self.expect_symbol(";")
        return ("exports", exported)

    def parse_imports(self) -> Node:
        self.expect_word("IMPORTS")
        groups: list[Node] = []
        if not self.at(";", "sym"):
            while True:
                symbols: list[Node] = []
                while not self.at_word("FROM"):
                    symbols.append(name(self.expect_reference()))
                    if self.at(",", "sym"):
                        self.advance()
                        continue
                    break
                self.expect_word("FROM")
                module_name = self.expect_type_name()
                if self.at("{", "sym"):
                    origin: Node = ("objectIdentifier", [literal(self.balanced("{", "}"))])
                else:
                    origin = ("objectIdentifier", [])
                groups.append(("from", [name(module_name), origin, *symbols]))
                if self.at(",", "sym"):
                    self.advance()
                    continue
                break
        self.expect_symbol(";")
        return ("imports", groups)

    def parse_assignment(self) -> Node:
        token = self.peek()
        if token.kind != "word":
            self.fail("a type or value assignment is required")
        if token.value[:1].isupper():
            spelling = self.expect_type_name()
            if self.at("{", "sym"):
                self.fail("parameterised types are not accepted")
            self.expect_symbol("::=")
            return ("typeAssignment", [name(spelling), self.parse_type()])
        spelling = self.expect_identifier()
        assigned = self.parse_type()
        self.expect_symbol("::=")
        return ("valueAssignment", [name(spelling), assigned, self.parse_value()])

    def parse_type(self) -> Node:
        if self.at("[", "sym"):
            return self.parse_tagged()
        base = self.parse_base()
        if self.at("(", "sym"):
            base = ("constrained", [base, literal(self.balanced("(", ")"))])
        return base

    def parse_tagged(self) -> Node:
        self.expect_symbol("[")
        if self.at_word("APPLICATION"):
            self.advance()
            tag_class = "application"
        elif self.at_word("PRIVATE"):
            self.advance()
            tag_class = "private"
        elif self.at_word("UNIVERSAL"):
            self.advance()
            tag_class = "universal"
        else:
            tag_class = "context"
        tag_number = self.expect_number()
        self.expect_symbol("]")
        if self.at_word("IMPLICIT"):
            self.advance()
            tagging = "implicit"
        elif self.at_word("EXPLICIT"):
            self.advance()
            tagging = "explicit"
        else:
            tagging = "absent"
        return (
            "tagged",
            [leaf(tag_class), number(tag_number), leaf(tagging), self.parse_type()],
        )

    def parse_base(self) -> Node:
        if self.at_word("CHOICE"):
            self.advance()
            return ("choice", self.bracketed(self.parse_alternative))
        if self.at_word("SEQUENCE"):
            self.advance()
            if self.at_word("OF"):
                self.advance()
                return ("sequenceOf", [self.parse_type()])
            return ("sequence", self.bracketed(self.parse_component))
        if self.at_word("SET"):
            self.advance()
            if self.at_word("OF"):
                self.advance()
                return ("setOf", [self.parse_type()])
            return ("set", self.bracketed(self.parse_component))
        if self.at_word("ENUMERATED"):
            self.advance()
            return ("enumerated", self.bracketed(self.parse_enumeration_item))
        if self.at_word("INTEGER"):
            self.advance()
            if self.at("{", "sym"):
                return ("integer", self.bracketed(self.parse_named_number))
            return leaf("integer")
        if self.at_word("BIT"):
            self.advance()
            self.expect_word("STRING")
            if self.at("{", "sym"):
                return ("bitString", self.bracketed(self.parse_named_number))
            return leaf("bitString")
        if self.at_word("OCTET"):
            self.advance()
            self.expect_word("STRING")
            return leaf("octetString")
        if self.at_word("OBJECT"):
            self.advance()
            self.expect_word("IDENTIFIER")
            return leaf("objectIdentifier")
        if self.at_word("CHARACTER"):
            self.advance()
            self.expect_word("STRING")
            return leaf("characterString")
        token = self.peek()
        if token.kind == "word" and token.value in PRIMITIVE_TYPES:
            self.advance()
            return leaf(PRIMITIVE_TYPES[token.value])
        if token.kind == "word" and token.value[:1].isupper():
            return ("named", [name(self.expect_reference())])
        self.fail("a type is required")
        raise AssertionError

    def parse_alternative(self) -> Node:
        if self.at("...", "sym"):
            self.advance()
            self.skip_exception()
            return leaf("extension")
        if self.at("[[", "sym"):
            return self.parse_extension_group(self.parse_alternative)
        spelling = self.expect_identifier()
        return ("alternative", [name(spelling), self.parse_type()])

    def parse_component(self) -> Node:
        if self.at("...", "sym"):
            self.advance()
            self.skip_exception()
            return leaf("extension")
        if self.at("[[", "sym"):
            return self.parse_extension_group(self.parse_component)
        if self.at_word("COMPONENTS"):
            self.advance()
            self.expect_word("OF")
            return ("componentsOf", [self.parse_type()])
        if self.peek().kind == "word" and self.peek().value[:1].islower():
            field: Node = name(self.expect_identifier())
        else:
            field = leaf("anonymous")
        assigned = self.parse_type()
        if self.at_word("OPTIONAL"):
            self.advance()
            presence: Node = leaf("optional")
        elif self.at_word("DEFAULT"):
            self.advance()
            presence = ("default", [self.parse_value()])
        else:
            presence = leaf("required")
        return ("component", [field, assigned, presence])

    def parse_enumeration_item(self) -> Node:
        if self.at("...", "sym"):
            self.advance()
            self.skip_exception()
            return leaf("extension")
        return self.parse_named_number()

    def parse_named_number(self) -> Node:
        spelling = self.expect_identifier()
        self.expect_symbol("(")
        if self.at("-", "sym"):
            self.advance()
            written = "-" + self.expect_number()
        elif self.peek().kind == "number":
            written = self.expect_number()
        elif self.peek().kind == "word":
            written = self.advance().value
        else:
            self.fail("a number is required")
            written = ""
        self.expect_symbol(")")
        return ("namedNumber", [name(spelling), number(written)])

    def parse_extension_group(self, parse_item) -> Node:
        self.expect_symbol("[[")
        version: list[Node] = []
        if self.peek().kind == "number" and self.ahead(":", "sym"):
            version = [number(self.expect_number())]
            self.expect_symbol(":")
        items = [parse_item()]
        while self.at(",", "sym"):
            self.advance()
            items.append(parse_item())
        self.expect_symbol("]]")
        return ("extensionGroup", version + items)

    def parse_value(self) -> Node:
        token = self.peek()
        if token.kind == "word" and token.value == "TRUE":
            self.advance()
            return ("booleanValue", [leaf("true")])
        if token.kind == "word" and token.value == "FALSE":
            self.advance()
            return ("booleanValue", [leaf("false")])
        if token.kind == "word" and token.value == "NULL":
            self.advance()
            return leaf("nullValue")
        if token.kind == "number":
            return ("integerValue", [number(self.expect_number())])
        if self.at("-", "sym"):
            self.advance()
            return ("integerValue", [number("-" + self.expect_number())])
        if token.kind == "string":
            return ("characterString", [literal(self.concatenate_strings())])
        if token.kind == "hex":
            self.advance()
            return ("hexString", [literal(token.value)])
        if token.kind == "bits":
            self.advance()
            return ("bitStringValue", [literal(token.value)])
        if self.at("{", "sym"):
            return self.parse_brace_value()
        if token.kind == "word" and token.value[:1].islower() and self.ahead(":", "sym"):
            spelling = self.expect_identifier()
            self.expect_symbol(":")
            return ("constructed", [name(spelling), self.parse_value()])
        if token.kind == "word" and token.value[:1].islower():
            return ("identifierValue", [name(self.expect_identifier())])
        self.fail("a value is required")
        raise AssertionError

    def parse_brace_value(self) -> Node:
        self.expect_symbol("{")
        if self.at("}", "sym"):
            self.advance()
            return ("sequenceValue", [])
        named = self.named_value_ahead()
        items = []
        while True:
            if named:
                items.append(self.parse_named_value())
            else:
                items.append(self.parse_value())
            if self.at(",", "sym"):
                self.advance()
                continue
            break
        self.expect_symbol("}")
        return ("sequenceValue" if named else "sequenceOfValue", items)

    def parse_named_value(self) -> Node:
        spelling = self.expect_identifier()
        return ("namedValue", [name(spelling), self.parse_value()])

    def named_value_ahead(self) -> bool:
        token = self.peek()
        if token.kind != "word" or not token.value[:1].islower():
            return False
        following = self.tokens[self.index + 1]
        return not (following.kind == "sym" and following.value in {",", "}", ":"})

    def bracketed(self, parse_item) -> list[Node]:
        self.expect_symbol("{")
        if self.at("}", "sym"):
            self.advance()
            return []
        items = [parse_item()]
        while self.at(",", "sym"):
            self.advance()
            items.append(parse_item())
        self.expect_symbol("}")
        return items

    def balanced(self, opener: str, closer: str) -> str:
        start = self.peek().start
        self.expect_symbol(opener)
        depth = 1
        while depth:
            token = self.peek()
            if token.kind == "eof":
                self.fail(f"unclosed '{opener}'")
            if token.kind == "sym" and token.value == opener:
                depth += 1
            elif token.kind == "sym" and token.value == closer:
                depth -= 1
            self.advance()
        return self.source[start:self.tokens[self.index - 1].end]

    def skip_exception(self) -> None:
        if self.at("!", "sym"):
            self.advance()
            if self.peek().kind in {"word", "number"}:
                self.advance()

    def concatenate_strings(self) -> str:
        text = self.peek().value
        self.advance()
        while self.peek().kind == "string":
            text += self.peek().value
            self.advance()
        return text

    def expect_type_name(self) -> str:
        token = self.peek()
        if token.kind != "word" or not token.value[:1].isupper():
            self.fail("a name beginning with an uppercase letter is required")
        self.advance()
        return token.value

    def expect_reference(self) -> str:
        token = self.peek()
        if token.kind != "word":
            self.fail("a name is required")
        self.advance()
        return self.qualified(token.value)

    def qualified(self, spelling: str) -> str:
        if self.at(".", "sym"):
            self.advance()
            rest = self.peek()
            if rest.kind != "word":
                self.fail("a name is required after '.'")
            self.advance()
            return spelling + "." + rest.value
        return spelling

    def expect_identifier(self) -> str:
        token = self.peek()
        if token.kind != "word" or not token.value[:1].islower():
            self.fail("an identifier beginning with a lowercase letter is required")
        self.advance()
        return token.value

    def expect_number(self) -> str:
        token = self.peek()
        if token.kind != "number":
            self.fail("a number is required")
        self.advance()
        return token.value

    def expect_word(self, expected: str) -> None:
        token = self.peek()
        if token.kind != "word" or token.value != expected:
            self.fail(f"'{expected}' is required")
        self.advance()

    def expect_symbol(self, expected: str) -> None:
        if not self.at(expected, "sym"):
            self.fail(f"'{expected}' is required")
        self.advance()

    def at_word(self, expected: str) -> bool:
        token = self.peek()
        return token.kind == "word" and token.value == expected

    def at(self, expected: str, kind: str) -> bool:
        token = self.peek()
        return token.kind == kind and token.value == expected

    def ahead(self, expected: str, kind: str) -> bool:
        token = self.tokens[self.index + 1]
        return token.kind == kind and token.value == expected

    def peek(self) -> Token:
        return self.tokens[self.index]

    def advance(self) -> Token:
        token = self.tokens[self.index]
        if token.kind != "eof":
            self.index += 1
        return token

    def fail(self, message: str) -> None:
        token = self.peek()
        line = self.source.count("\n", 0, token.start) + 1
        column = token.start - self.source.rfind("\n", 0, token.start)
        found = "end of input" if token.kind == "eof" else token.value
        raise ParseError(f"line {line}, column {column}: {message}; found {found}")


PRIMITIVE_TYPES = {
    "BOOLEAN": "boolean",
    "NULL": "null",
    "UTF8String": "utf8String",
    "IA5String": "ia5String",
    "NumericString": "numericString",
    "PrintableString": "printableString",
    "VisibleString": "visibleString",
    "GraphicString": "graphicString",
    "GeneralString": "generalString",
    "UniversalString": "universalString",
    "BMPString": "bmpString",
    "TeletexString": "teletexString",
    "VideotexString": "videotexString",
    "ObjectDescriptor": "objectDescriptor",
    "GeneralizedTime": "generalizedTime",
    "UTCTime": "utcTime",
    "REAL": "real",
    "DATE": "date",
    "TIME": "time",
    "DATE-TIME": "dateTime",
    "DURATION": "duration",
    "RELATIVE-OID": "relativeOid",
    "TIME-OF-DAY": "timeOfDay",
}


def tokenize(source: str) -> list[Token]:
    tokens: list[Token] = []
    index = 0
    length = len(source)
    while index < length:
        character = source[index]
        if character.isspace():
            index += 1
            continue
        if source.startswith("--", index):
            index += 2
            while index < length and source[index] != "\n":
                index += 1
            continue
        if source.startswith("/*", index):
            close = source.find("*/", index + 2)
            if close < 0:
                raise ParseError(_located(source, index, "unclosed comment"))
            index = close + 2
            continue
        for symbol in ("::=", "...", "..", "[[", "]]"):
            if source.startswith(symbol, index):
                tokens.append(Token("sym", symbol, index, index + len(symbol)))
                index += len(symbol)
                break
        else:
            if character == '"':
                tokens.append(_string_token(source, index))
                index = tokens[-1].end
            elif character == "'":
                tokens.append(_marked_string_token(source, index))
                index = tokens[-1].end
            elif character.isalpha():
                tokens.append(_word_token(source, index))
                index = tokens[-1].end
            elif character.isdigit():
                end = index + 1
                while end < length and source[end].isdigit():
                    end += 1
                tokens.append(Token("number", source[index:end], index, end))
                index = end
            elif character in "{}()[],:;[]@|!<>^.-":
                tokens.append(Token("sym", character, index, index + 1))
                index += 1
            else:
                raise ParseError(_located(source, index, "this character is not accepted"))
    tokens.append(Token("eof", "", length, length))
    return tokens


def _string_token(source: str, start: int) -> Token:
    index = start + 1
    characters: list[str] = []
    while index < len(source):
        if source[index] == '"':
            if source.startswith('""', index):
                characters.append('"')
                index += 2
                continue
            return Token("string", "".join(characters), start, index + 1)
        if source[index] == "\n":
            raise ParseError(_located(source, start, "a character string is not closed"))
        characters.append(source[index])
        index += 1
    raise ParseError(_located(source, start, "a character string is not closed"))


def _marked_string_token(source: str, start: int) -> Token:
    close = source.find("'", start + 1)
    if close < 0 or close + 1 >= len(source):
        raise ParseError(_located(source, start, "a binary or hexadecimal string is not closed"))
    mark = source[close + 1]
    contents = source[start + 1:close]
    if mark in "Hh":
        if contents and any(character not in "0123456789abcdefABCDEF" for character in contents):
            raise ParseError(_located(source, start, "a hexadecimal string contains a non-hexadecimal digit"))
        return Token("hex", contents, start, close + 2)
    if mark in "Bb":
        if contents and any(character not in "01" for character in contents):
            raise ParseError(_located(source, start, "a binary string contains a digit other than 0 or 1"))
        return Token("bits", contents, start, close + 2)
    raise ParseError(_located(source, start, "a binary or hexadecimal string must end in B or H"))


def _word_token(source: str, start: int) -> Token:
    index = start + 1
    while index < len(source):
        character = source[index]
        if character.isalnum():
            index += 1
            continue
        if character == "-" and index + 1 < len(source) and source[index + 1] not in "-":
            index += 1
            continue
        break
    if source[index - 1] == "-":
        raise ParseError(_located(source, start, "a name must not end with a hyphen"))
    return Token("word", source[start:index], start, index)


def _located(source: str, index: int, message: str) -> str:
    line = source.count("\n", 0, index) + 1
    column = index - source.rfind("\n", 0, index)
    return f"line {line}, column {column}: {message}"


def main(argv: list[str]) -> int:
    if len(argv) <= 1:
        sys.stdout.write(translate(sys.stdin.read()))
        sys.stdout.write("\n")
        return 0
    for path in argv[1:]:
        with open(path, encoding="utf-8") as handle:
            sys.stdout.write(translate(handle.read()))
            sys.stdout.write("\n")
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main(sys.argv))
    except ParseError as error:
        sys.stderr.write(f"{error}\n")
        raise SystemExit(1)
