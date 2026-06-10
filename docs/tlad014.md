# Cryptography in SPaDE

In this document we sketch the use of cryptography in SPaDE to provide assurance of the integrity of the deductive system and to enable confidentiality where required.

At present the following uses of cryptographic hashes are envisaged:

- Signing of Repo Increments
- Hash of Context for each theorem
- Hash of Theorem Content (including context hash)

Theorems will be signed by the authority undertaking the inference or otherwise affirming truth.
This involves the establishment of a calculus of authorities and authority levels.

## Repo Increments

## Context Hashes

## The Calculus of Authority Levels

The exposition falls into the following parts:

- Authorities
- Authority Levels
- Qualified Theorems

### Authorities

An authority is a cryptographic key pair used to sign theorems.

### Authority Levels

The derivation of a theorem begins with theorems already present in the repository which will themselves have been signed by some authority.
Confidence in the theorem depends not only the reliability of the signing authority, but also on that of the authorities whose theorems were used in the proof of the theorem.
The form of theorems in SPaDE therefore make provision to record the other authorities which have contributed to the proof of the theorem prior to the derivation which the signing authority is endorsing.

These complications give rise to a calculus of authority levels.

The steps contributing to this calculus are as follows:

1. A theorem may be thought of as conditional on the infallibility of the authorities which have contributed to its proof.
We therefore think of the theorem as conditional on the infallibility (subject to some qualification) of the authorities which have contributed to its proof, and the authority level of a set of authorities is the conjunction of the infallibility of those authorities.
2. If we should have more than one proof of a theorem, then our confidence is improved, since the infallibility of either set of authorities would be sufficient to guarantee the truth of the theorem, and the authority level of the theorem is therefore the disjunction of the authority levels of the proofs.
3. To avoid having to use very complex expression for authority levels we admit that authority levels can be named which are not themselves used for signing, but may appear in theorems.
This mechanism allows for the establishment of certification authorities which may give confidence in authorities by their own assessments and may therefore be used by third parties in chosing the level of authority which they require for their applications.

### Qualified Theorems

An authority level is a positive boolean expression of authority levels or authorities.

Each theorem is qualified by an authority level, which captures the authorities which have constributed to the theorems used in its derivation.
It is also given a sequence number which is a strict supremum of the sequence numbers of the theorems used.

The theorem also includes a checksum of the context in the SPaDE repository in which it was derived.

Finally the content of the theorem is a HOL term which the truth of which is affirmed by the derivation.

The above components form the package (i.e. the "message") which is signed by the authority endorsing the theorem.

The public key may be stored in a SPaDE repository. The authority may be located by the repository path of that public key, while the private key must be stored separately by its owner, for example in a secure store or a private repository.

[The above needs to be worked out more fully elsewhere, this document is intended to be a philosophical sketch on the relationship between philosophical scepticism and the SPaDE architecture.]

## Authority and Scepticism through the Epistemic Stack

The above discussion of authority and scepticism primarily related to confidence in the establishment of logical or analytic truth in SPaDE, and it is held that it admits the achievement of high levels of confidence in such truths.

At the coarsest level of granuality synthetic epistemology admits two other division of declarative knowledge,
empirical, and normative.
The semantics of these other kinds of declarative knowledge is mediated by abstract models, and confidence in their truth is therefore dependent on the relationship between the abstract models and the structure of the real world (in the former case) or that of culturally evolved norms.

Whereas in the context of the chosen linguistic conventions purely logical or analytic claims can be said to have definite and objective truth values, the situation is more complex for the other kinds of proposition.

Abstract models of the real world are in general mere approximations to its structure.
The status of a declarative proposition in relation to such an abstract model when fullyy stated involved mutliple elements as follows:

- The truth value of the proposition in the context of the abstract model.
- Some appropriate measure of the fidelity of the abstract model to those aspects of the real world it is intended to represent.
- Identification of the portion of the real world to which the model has been applied.
This fixes the edge conditions which instantiate the abstract model for this application.
