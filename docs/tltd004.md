# Task Description: The Theory of T-expressions

## Introduction

The task is to complete the ProofPower HOL specification of the theory `T_ex` in [tlcd004.md](tlcd004.md), until ProofPower accepts the script.

The theory is a child of `SPaDEroot`. It is not named after the document. The prelude and the consistency mechanism it uses are in [tlcd002.md](tlcd002.md). The procedure for a ProofPower specification in markdown is [admin/ampd012.md](admin/ampd012.md). The paragraph characters are `ⓈHOLCONST` and `│`, as in [tlcd002.md](tlcd002.md) and [admin/amms012.md](admin/amms012.md).

The specification to be met is the text of [tlcd004.md](tlcd004.md). In particular, the encoding table there is the witness for `pack_bytes`. The sentence in [../kr/krdd004.md](../kr/krdd004.md) that writes every byte `1` as `1 1` is not the rule.

The formal paragraphs in the draft are the target. They are not in `sml` fences. [tlci001.mkf](tlci001.mkf) already loads the document, and the only `sml` fence creates the empty theory `T_ex`. A stage is checked by moving its paragraphs into `sml` fences.

## Stages

The stages are carried out in [tlcd004.md](tlcd004.md). Each stage leaves a script that ProofPower accepts before the next stage adds to it.

1. Define witnesses for `pack_bytes` and `unpack_bytes` by the encoding in the draft. Prove the peel property: for every string `s` and every remainder `rest`, unpacking `pack_bytes s` appended to `rest` returns `(s, rest)`.
2. Save that existence theorem with `save_cs_∃_thm`, select the proof context `'savedthm_cs_∃_proof`, and introduce `pack_bytes` and `unpack_bytes` with the peel property as their specification.
3. Define `pack_list` as the concatenation of those null-terminated codings, and prove that repeated unpacking recovers the list.
4. Define the inductive set of representations of `mk_T_ex (s, ts)`, prove it non-empty, and introduce the type `T_ex` with `mk_T_ex` and `dest_T_ex` as mutual inverses. The representation set is that inductive subset. It is not the whole range of `pack_list`.

## Check

`tlcd004.md` is already in `PPMDLOAD` in [tlci001.mkf](tlci001.mkf), and `tlcd004.ldd` depends on `tlcd002.ldd`. From `docs/`, with `PPDIR` set, in the ProofPower image:

```sh
make -f tlci001.mkf tlcd004.ldd
```

The stage is complete when the log contains no error. `make build` also loads `tlcd001` and `tlcd003`. A failure in those documents is not a failure of this task.

The abstract-syntax theory in [tlcd001.md](tlcd001.md) can take `T_ex` as a parent after this theory loads. That change is not part of this task.
