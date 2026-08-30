# Independent review: Grok authors, Copilot reviews

This is the working practice for the period in which **Grok Build** (with the human) does the work, and **GitHub Copilot** is used as an *independent* reviewer of that work. It complements [ampd004.md](ampd004.md) (branches, worktrees, sessions) and does **not** revive Copilot as the primary authoring agent ([ampd001.md](ampd001.md), [ampd002.md](ampd002.md)).

## Roles

| Role | Who | Does |
|---|---|---|
| Author | Human + Grok Build, in an area worktree | Design and write; keep outcomes in `docs/` (and code when that area is in scope) |
| Independent reviewer | GitHub Copilot **code review** on a pull request | Read the PR diff; post review comments without having written the change |
| Integrator | Human | Merge to `main` only after the PR (and Copilot review) have been considered |
| Fallback chat | Copilot Chat in VS Code | Interactive questions when Grok is unavailable; not a substitute for PR review |

Independence here is **institutional**, not metaphysical: Copilot did not produce the patch, and it sees the GitHub PR, not the Grok session transcript. It can still be wrong, shallow, or aligned with GitHub/Microsoft defaults. The human remains the integrator.

## Updates to `main` go through a pull request

Do not merge an area branch into `main` from the worktree as a silent fast-forward when Copilot review is expected.

1. Finish a **coherent unit** on the area branch (`am`, later `kr`, `mcp`, …).
2. Push the branch and open a PR **into `main`**.
3. Request **Copilot as a reviewer** (GitHub UI: Reviewers → Copilot; CLI: `gh pr edit N --add-reviewer copilot`; MCP: `request_copilot_review`).
4. Read Copilot’s comments. Accept, reject, or park them in the PR or in `reviews/` as appropriate. Grok may help *respond* to the review; it must not pretend the review was independent if it then rewrites the patch to match Copilot uncritically without the human noticing.
5. Merge only when the human is satisfied. Copilot is not a required green check unless a branch-protection rule is later added.

Draft PRs are allowed when early Copilot feedback is useful; mark ready before merge.

## Choosing how Copilot reviews

Two GitHub features are easy to confuse:

**Copilot code review** (the reviewer on the PR) is the independent-review path. As of 2026-08, GitHub exposes **effort levels** for that review (**Lite** vs **Balanced**), and org/repo defaults, not a full chat-style model picker on `gh pr` / the GitHub MCP `request_copilot_review` call (that MCP method has no model field). Community requests for `--copilot-model` on `gh pr` are still product feedback.

**`@copilot` in a PR comment** can show a **model picker**. That path is Copilot **coding agent** (implement / follow-up edits), not the independent code-review reviewer. Use it only when we *want* Copilot to write a follow-up, which is a different role.

Until GitHub offers a durable API for “review this PR with model X”:

- Prefer **Balanced** (or the then-current deeper effort) for documentation architecture and anything that will land on `main`.
- Use **Lite** for tiny, mechanical PRs if effort selection is available in the UI.
- If a model must be named, do it in a **PR comment** after the review, e.g. asking Copilot Chat / coding agent to *explain* a finding with a chosen model — that is not a second independent review of the same patch.
- Record in the PR (or `reviews/`) which surface ran (code review vs `@copilot`) and, when the UI shows it, effort level or model.

Re-check GitHub’s Copilot review docs when this procedure is used; the product moves.

## What this is not

- Not Copilot authoring a PR that Grok then “reviews.” That inverts the independence we want.
- Not `/resume-codex` or a third agent (Claude Code, Codex CLI). Those remain uninstalled unless deliberately adopted.
- Not automated evaluation of SPaDE **as a tool for LLMs**. That is a later, separate problem (see below).

## Later: evaluating SPaDE as support for LLMs

Once KR/MCP are far enough to *use*, the primary evaluation is whether other models (Copilot’s, Grok’s, others) can **retrieve, cite, and reason with** repository content through the MCP (and related) interfaces.

Open questions, not yet decided:

1. **Subjects vs authors.** The model under test should be a *client* of SPaDE, not the agent that just wrote the docs. Copilot is a natural first subject because it is already in the PR loop; it should not be the only one.
2. **What is scored.** Retrieval (right fragment, right context), citation discipline, refusal when the repo is silent, and success on small perfect-information tasks in a declared context — not “sounds like philosophy.”
3. **Automation.** Likely a frozen prompt set + MCP session log + a judge that is *not* the subject model. GitHub Actions can run the harness; Copilot code review of *harness PRs* is not the same as running the harness.
4. **Contamination.** Prompts and gold answers live outside the session that authored the KR slice under test.
5. **Human gold.** Early items need a human-agreed expected use of the docs; later, the KR’s own contexts may supply the gold.

Do not invent a scoring dashboard before there is an MCP surface worth calling. When that work starts, put methods under **Testing and evaluation** in [README.md](README.md), not only in chat memory.
