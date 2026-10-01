# Documentation

These guides describe the current library, not its sequence of implementation
stages. Start with a program in the case guide; consult theorem owners for full
signatures and proof details. Historical proposals and acceptance logs live in Git.

| Guide | Read it for |
| --- | --- |
| [Architecture](ARCHITECTURE.md) | Imports, relation ownership, canonical routing, dependency and test boundaries |
| [Theory](THEORY.md) | Generic algebra, bind, structural bridges, up-to reasoning and model obligations |
| [Iteration](ITERATION.md) | Eventful congruence, full uniformity, complete-frontier summaries and classical lfp compatibility |
| [Interpreters](INTERPRETERS.md) | Handler algebra, State/Reader/Writer/Exception, transformer folds and ITree conservativity |
| [MDP and transitions](MDP.md) | Labelled comparison semantics, fragment coincidence and faithful kernel encoding |
| [Backends](BACKENDS.md) | Finite rational/real representations, MathComp capabilities and Gate M |
| [FreeOmega soundness](FREEOMEGA_SOUNDNESS.md) | Independent probability model, modelability, hitting adequacy and external joints |
| [Execution](EXECUTION.md) | Fold, closed runner, rational sampling, finite correctness and fuel-free simulation |
| [Case studies](CASE_STUDIES.md) | Reading entries, notation and the role of each program proof |
| [Case-study standard](CASE_STUDY_STANDARD.md) | Presentation and proof-organization policy |
| [Verification](AUDITING.md) | Local commands, contract data and checked/unchecked trust contexts |

Machine-readable contracts and the generated dependency inventory belong in
[`tools/data/`](../tools/data/), not alongside narrative guides. They are not
optional documentation: maintained tools consume them. No snapshot is refreshed
merely because its file moves.

Keep new explanations in the relevant guide or source comment. A new lemma,
commit or development phase does not need another Markdown report. Add a new
guide only for a genuinely separate reader task, not to preserve progress logs.
