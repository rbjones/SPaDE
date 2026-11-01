# Knowledge Representation Meta-Task-Description

## Introduction

This meta-task covers the knowledge representation subsystem within the SPaDE project.
It is concerned with the subsystems mediating persistent storage of declarative knowledge and the components of SPaDE which apply that knowledge by deductive methods.

The first stored form to be supported is the SPaDE native repository, in which the SPaDE local repository is stored in serial binary file as an NTBSS (Null-Terminated Byte Sequence Sequence) WORM store.

The sewing together of these local repositories into the diasporic repository required access to multiple such local repositories which together contribute the various logical contexts (theories)in which work can be conducted.

Early tasks will implement access to single local repositories in layers, starting will a low level T-expression interface.