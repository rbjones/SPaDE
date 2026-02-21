# SPaDE Knowledge Repository Information Structures

## Introduction

The purpose of this document is to describe in some detail the structure of SPaDE repositories and of the views of the repositories presented by the kr subsystem  to other subsystems of SPaDE and to the clients of the SPaDE MCP server.

Local SPaDE repositories combine together to yield a single name-space assigning meaning to names.
These names provide abstract language which may be used in declarative propositions describing or deriving conclusions about abstract structures modelling structures of interest.

At the highest level of abstraction the namespace has three levels, these are called "pansophic", "diasporic", and "local".
The pansophic level encompasses the whole universe, and consists of a set of mutually isolated diasporic repositories each of which is a maximal connected space of the pansophic knowledge repository.

Each diasporic repository is a hierarchy in which individual names are paths from the root of the diasporic repository.
These paths are not absolute, but are relative to the root of the diasporic repository.
When diaspora make contact, the individual diaspora merge either by the incorporation of one into the other, or by the creation of a new repository above each, extending the diasporic paths on with an extra element on the left.

A diasporic repository is a composed of local repositories, each distinguished by a unique path from the root of the diasporic repository.
The full diasporic path of a name is the concatenation of the diasporic path to a local repository with a path within that local repository.

The pansophic repository as a whole is therefore a set of diasporic name-spaces each of which assigns meaning to paths in a diaspora.
The pansophic repository advances by the creation of new diaspora (as new sources of intelligence evolve) augmentation of existing diaspora by the addition of new paths and constraints defining their meaning, or by the combination of two or more existing diaspora.
The augmentation of diaspora leaves unchanged the meanings assigned to existing paths in the diaspora.
All references to names are provided by relative paths from a location which is called the context of the reference.
Such references are stable under all the permitted diasporic changes.

The constraints which give meaning to names in the repository mention other names already present in the diasporic repository, and the transitive closure of the resulting relationship of dependence gives a partial ordering on the names in the diasporic repository.
A coarse version of this ordering comes from a parent-child relationship between theories in the repositories, which acts as a limitation on the visibility of names at any location in the repository.

## Introduction (II)

*this should be incorporated or deleted*

  At the pansophic level, the information space is unlikely every to be wholly connected, since  intelligent systems will originate from a variety of diverse points in the universe and communication across cosmic distances takes time.
  The information space will be partitioned into a variety of repositories, distributed across the Cosmos. 
  At the diasporic repository level, the information space is connected, and is structured as a directed acyclic graph of NTBSs (Named Typed Binary Structures), which are the basic units of information in SPaDE.  At the NTBS level, the information space is connected, and is structured as a directed acyclic graph of components, which are either atomic values or references to other NTBSs.
