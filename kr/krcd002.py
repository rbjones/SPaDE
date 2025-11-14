# Python translation of kr/krdd001.md HOL datatypes

from dataclasses import dataclass
from typing import List, Tuple, TypeVar, Generic, Union


# Names
@dataclass
class RName:
    n: int
    pairs: List[Tuple[str, int]]


# HName Trees
A = TypeVar('A')


class Hntree(Generic[A]):
    pass


@dataclass
class Hnt(Hntree[A]):
    label: str
    children: List[List['Hntree[A]']]


@dataclass
class Hleaf(Hntree[A]):
    value: A


# Types
@dataclass
class Tyv:
    rname: RName


@dataclass
class Tyc:
    rname: RName
    types: List['Htype']


Htype = Union[Tyv, Tyc]


# Terms
@dataclass
class Tmv:
    rname: RName


@dataclass
class Tmc:
    rname: RName


@dataclass
class Tapp:
    left: 'Hterm'
    right: 'Hterm'


@dataclass
class Tabs:
    rname: RName
    htype: Htype
    hterm: 'Hterm'


@dataclass
class Trel:
    rname: RName
    hterm: 'Hterm'


@dataclass
class Tloc:
    rname: RName
    hterm: 'Hterm'


Hterm = Union[Tmv, Tmc, Tapp, Tabs, Trel, Tloc]


# Sequents
@dataclass
class Hsequent:
    hyps: List[Hterm]
    concl: Hterm

