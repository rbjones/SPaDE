Review of Glossary Augmentation Test Run

**Date**: 2025-11-03
**Time (UTC)**: 19:41
**Reviewer**: rbjones
## Overview

This review evaluates the glossary augmentation procedure as executed by Copilot on 2025-11-03. The process followed the two-stage workflow outlined in `docs/admin/amms007.md`, resulting in the addition of several new terms to the SPaDE project glossary.

## Stage 1 Assessment

The following issues are noted in the new links created to the glossary.

### README.doc
We see here that an emphasised phrase *fundamental imperative of evolution* has a link on a single word.
The guidelines should discourage this.  The highlighting is clearly intended to indicate that the phrase as a whole is a significant and perhaps original concept.

There is an incorrect link on the phrase *focal intelligence* which points to `docs/tlad001.md#focal-intelligence-or-focal-ai`.  This appears to pre-date the augmentation, but this is easily detected since all links to the glossary should be to the phrase linked.
Fixing this kind of error probably belongs in the separate process checking for broken links.

### di/README.md

The link on *deductive intelligence* is incorrect.
It does not point to the glossary file and the anchor is wrong.
It should be `../docs/tlad001.md#deductive-intelligence`.

### dk/README.md

The link on *deductive kernel* is inappropriate.
I'm not sure what principle this should be based on.

### docs/admin/ampl001.md

I see now that "focal-intelligence or focal-ai" has been added to the glossary, but is not an item which can be linked to, so the link would have to point to focal.
However, recent policy change suggests that the list under "focal" should be replaced by #### level subsections for each of the items in the list, so that they can be linked to directly.

### kr/krad001.md

More examples of phrases linking to the top of the document in which they occur.
We need a policy to discourage this.

