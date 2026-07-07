# Proofreading review: process-calculi-and-concurrency.tex

Reviewed 2026-07-06 (full 2,192-line read; all Lean code compiled against toolchain
leanprover/lean4:v4.31.0, core Lean only — no Mathlib, matching the book's stated
setup). Companion verification file: `PiCalcVerification.lean` (compiles clean; one
`sorry` = Exercise 5.2, the book's own exercise; every fix marked `DEVIATION`). Line
numbers refer to the .tex. `PiCalc.lean` is the reader's own workthrough and is still
empty ("-- Not started"), so it provided no divergence evidence.

## Verdict

Solid survey. The core theory (LTS, CCS syntax and operational semantics, the
coffee-machine bisimulation counterexample, HM logic and its adequacy theorem, session
duality) is correct, and — unlike the sibling calculus book — the "no Mathlib, build
everything from scratch" claim (l.263) genuinely holds: every Lean listing compiles in
core Lean. Two printed Lean listings do NOT compile as written (the CCS notation block,
and the capstone `worker`), and there is a real theory error in the λ-calculus encoding
(Ch 6), plus a factual error in the Preface (Ariane 5). The biggest structural gap is
that the π-calculus is given syntax in Lean but never a substitution function or a step
relation, yet several exercises ("prove in Lean") depend on machinery the book never
provides. None of the errors are fatal to the book's arc; all are locally fixable.

## Math errors

1. **l.232 (Preface) — Ariane 5 is not a concurrency failure.** "The Ariane 5 rocket
   exploded because of a concurrent sensor processing fault." Flight 501 (1996) failed
   because a 64-bit floating-point horizontal-velocity value was converted to a 16-bit
   signed integer, overflowed, and raised an unhandled Operand Error in reused Ariane 4
   alignment code — a data-conversion/overflow bug, not a race condition or concurrency
   fault. Using it as a concurrency cautionary tale is inaccurate. (The Therac-25
   example beside it is correct.)

2. **ll.1161–1170 — the λ-calculus → π encoding as printed does not reduce.** With
   `⟦λx.M⟧_u = u(x,v).⟦M⟧_v` (an **input** on u) and
   `⟦MN⟧_u = (νv)(⟦M⟧_v | v(x,w).(⟦N⟧_x | w̄⟨u⟩.0))`, take a redex `(λx.M)N`:
   `⟦λx.M⟧_v = v(x,v').⟦M⟧_{v'}` is an **input** on v, and the surrounding context
   `v(x,w).(…)` is **also an input** on v. Nothing ever outputs on v, so the redex is
   stuck — no τ step is possible. Milner's encoding requires the application side to
   **output** on v (send the argument-access and return channels to the abstraction).
   The printed polarity is reversed. Exercise 6.2 (ll.1191–1196) then asks the reader
   to trace `(λx.x) y` "and verify the result is y", which cannot be done with the
   printed rules. Secondary problem: the encoding uses polyadic tuples `(x,v)`, `(x,w)`
   that the monadic syntax (Def, ll.1076–1092, single-name `x̄⟨y⟩`/`x(y)`) never
   introduces. Fix: present a correct monadic Milner encoding, or clearly flag this as
   an informal polyadic sketch and correct the send/receive polarity on v.

3. **ll.1130–1134 — scope-extrusion reduction omits its side condition.** The step
   `(νa)(x̄⟨a⟩.P) | x(z).Q ⟶τ (νa)(P | Q[a/z])` is only sound when `a ∉ fn(Q)` (else the
   widened `νa` scope captures a name already free in the receiver). The book states the
   analogous side condition for the structural-congruence law at l.1257
   (`(νa)(P|Q) ≡ P | (νa)Q  if a ∉ fn(P)`), so the omission here is an internal
   inconsistency as well as a correctness gap. Add `a ∉ fn(Q)` (equivalently, choose `a`
   fresh for the right-hand process).

4. **l.676 — the Comm rule is stated in only one direction.** As written,
   "If P →a P' and Q →ā Q' then P|Q →τ P'|Q'" covers only P-input/Q-output. The
   symmetric case (P output, Q input) is not literally an instance unless one adds "or
   symmetrically" or lets the label range over complements. The Lean model correctly
   adds the missing direction (`commR`), so the prose Def is the weaker of the two.
   Minor, but worth a one-line "and symmetrically" in the Def.

5. **ll.958–962 — the deadlock explanation mislabels the blocker.** With
   `A = b̄.a.0`, `B = ā.b.0`, the text says "A is waiting for input on a … and B is
   waiting for input on b." But A's *first* and blocking action is an **output** on b;
   it never reaches its input on a. The real deadlock is two senders with no matching
   receivers (A wants to send on b, nobody receives on b; B wants to send on a, nobody
   receives on a). The example and the restriction are correct — only the prose gloss
   is muddled. (Machine-checked: `deadSys` in the verification file; the no-transition
   half is Exercise 5.2, left as `sorry`.)

## Lean errors

6. **ll.651–654 — the CCS notation block is placed at top level and does not compile.**
   The four `scoped notation`/`scoped infixr/infixl` declarations produce
   `error: Scoped attributes must be used inside namespaces` (reproduced). `scoped`
   requires an enclosing `namespace`. Fix: wrap them in a `namespace … end`, or drop the
   `scoped` keyword. (Verification file: placed in `namespace CCSNotation`.)

7. **ll.1876–1885 — the capstone `worker` fails termination checking.** It is a plain
   `def` that recurses as `worker pool` — same argument, no decreasing measure — so Lean
   rejects it: `fail to show termination for worker … it is unchanged in the recursive
   calls … does not take any (non-fixed) arguments`. The intent is a non-terminating
   server loop, so the honest fix is `partial def worker` (which additionally requires a
   `Nonempty`/`Inhabited Pi` instance — supplied in the verification file). `dispatcher`
   just above it (ll.1863–1873) is fine: it recurses structurally on `tasks`.

8. **Structural gap: the π-calculus has no operational semantics or substitution in
   Lean.** The prose comm rule uses `Q[y/z]` (l.1124), but substitution `[y/z]` is never
   implemented in Lean; `Pi` (ll.1097–1116) gets only `freeNames`, and there is no
   `PiStep` relation anywhere in the book (CCS gets `CCSStep`, π gets nothing). As a
   result the "prove in Lean" exercises that target π — Exercise 6.2 (trace the encoding)
   and Exercise 12.2 (prove the worker pool deadlock-free "using the π-calculus
   operational semantics") — ask the reader to build on Lean machinery the book never
   provides. Either add a π-calculus `subst` + `PiStep` (a substantial but standard
   addition) or reword those exercises as pencil-and-paper.

Everything else compiles verbatim: `Action`/`LTS`, `VMStep`, `CCSAct`/`complement`/
`CCS`, `CCSStep`, `IsBisimulation`/`Bisimilar`, `isDeadlocked`, both `philosopher`
defs, `Pi`/`freeNames`, `StructCong`, `HML`/`Satisfies`, `BaseType`/`SessionType`/
`dual`/`dual_dual` (the `dual_dual` involution proof runs exactly as printed), `Role`/
`GlobalType`, and `dispatcher`.

## Learning gaps

9. **No tactic primer, but tactic-based proofs appear and are assigned.** Prerequisites
   (l.259) assume "comfort with Lean 4 … tactics," yet the only worked tactic proof in
   the book is `dual_dual` (`induction … with`, `simp`, `rfl`). Exercises then ask for
   nontrivial tactic/derivation proofs — construct a `CCSStep` derivation (Ex 3.2),
   prove non-bisimilarity (Ex 4.2), prove the adequacy ⇒ direction by induction on φ
   (Ex 8.2). The sibling calculus/order-lattices books gained tactic-primer appendices;
   this one would benefit from at least one fully worked `CCSStep` derivation (the
   verification file supplies the two-step request/response derivation as a model) and a
   short note on `induction … with`/`simp`.

10. **P + Q ↔ `Promise.race` (l.738) is an imperfect analogy.** CCS choice `+` *discards*
    the branch not taken; `Promise.race([p,q])` resolves with whichever settles first but
    leaves the losing promises **running** (their side effects still happen). Worth a
    one-line caveat so a SWE reader does not over-trust the mapping.

11. **HML "specification" examples use notation outside the defined grammar (ll.1387–1396).**
    `[τ]*⟨req⟩tt` uses an iterated/Kleene-star modality and
    `live = ⋁_a ⟨a⟩tt` uses an infinite disjunction; the HML grammar (Def, ll.1315–1330)
    has neither iteration nor n-ary/infinite connectives. Fine as motivation, but should
    be flagged "informally / beyond the core logic (this is really the modal μ-calculus)."

12. **Session-type / multiparty safety theorems are asserted, not verified.** Thm 9
    (session safety), Thm 11 (multiparty safety), and the three capstone theorems (12)
    have English proof sketches only and no Lean, while the capstone chapter is titled
    "Verified Worker Pool Protocol." Reasonable for a survey, but "verified" oversells
    what is actually machine-checked (only `dual_dual` and, in this companion file, two
    small `CCSStep` derivations). A sentence distinguishing "proved on paper" from
    "checked in Lean" would set expectations.

## Internal inconsistencies (minor)

13. **StructCong (Lean, ll.1268–1281) omits the laws the Def (ll.1248–1263) headlines.**
    The inductive encodes only the six algebraic laws (par comm/assoc/nil, plus
    comm/nil/idem) plus equivalence + congruence closure, and drops all four laws that
    are *specific* to structural congruence in the Definition: `(νa)0 ≡ 0`,
    `(νa)(νb)P ≡ (νb)(νa)P`, scope extrusion, and `!P ≡ P | !P`. It also lacks a
    `resCong`. It is a CCS-only subset presented as if it realized Def 7.x; note the
    scope or add the missing constructors.

14. **Comm math rule vs Lean (see finding 4):** the Def gives one Comm direction, the
    Lean gives two (`comm`, `commR`). Harmonize.

15. **Appendix B "Lean 4 Definitions Index" (ll.2138–2159) is incomplete.** It omits
    `CCSAct.complement`, `Pi.freeNames`, `philosopher`, `dispatcher`/`worker`, `Role`,
    `BaseType`, and the `dual_dual` theorem, while listing the headline defs. Cosmetic.

## Verification summary

- Lean listings in the book: 18 `leanbox` code blocks. All 18 reproduced in
  `PiCalcVerification.lean`.
- Compile status: **clean** on leanprover/lean4:v4.31.0, core Lean only.
- Fixes required to compile (marked `DEVIATION`): 2 — the `scoped` notation block must
  live inside a namespace (finding 6); `worker` must be `partial def` + a `Nonempty Pi`
  instance (finding 7). All other listings compile exactly as printed.
- `sorry` count: 1, and it is the book's own Exercise 5.2 (deadlock of `(νa)(νb)(A∥B)`);
  the theorem *statement* is included and type-checks.
- Printed `#eval`/simulator outputs to confirm: **none** — the book prints no `#eval`s
  and no executable simulator, so there are no runtime outputs to check.
- Extra machine checks added (not in the book, as evidence for the prose): the
  request/response worked example reduces in exactly two τ steps (Ex 3.2 derivation);
  reflexivity of `Bisimilar` via the identity relation (supports Thm "bisimilarity is an
  equivalence"); `dual_dual` runs as printed.

## Coverage

Full sequential read of all 2,192 lines. Theory checked by hand: CCS grammar and SOS
rules (Prefix/Choice/Par/Comm/Res/Repl), the request/response derivation (re-derived,
correct), the coffee-machine trace-vs-bisimulation counterexample (correct), the
send-first deadlock (correct; prose gloss flagged), π-calculus comm and scope extrusion
(side condition flagged), the λ-encoding (broken — flagged), structural congruence laws,
HM logic satisfaction and the distinguishing formula (correct) and adequacy statement
(correct, image-finiteness stated), session-type duality and its involution (correct),
multiparty projection (partial sketch, fine). All 18 Lean listings extracted, compiled,
and cross-checked against the prose. Historical claims spot-checked (Dijkstra 1965/1968,
Milner CCS 1980 / π 1992 / Turing 1991, Park 1981, Hoare 1978/1985, Hennessy–Milner
1985, Honda 1993 and 1956–2012, Honda–Yoshida–Carbone 2008, Wadler 2012, Clarke–Emerson–
Sifakis 2007, O'Hearn Gödel 2016) — all correct except Ariane 5 (finding 1). TypeScript
listings read for accuracy (event loop, worker_threads, MessageChannel transfer/scope
extrusion — all sound); they were not compiled (no TS toolchain in scope).

## Resolution (2026-07-06)

All findings patched in place in `process-calculi-and-concurrency.tex`; every
printed Lean listing (and every primer example) is mirrored and compile-checked
in `PiCalcVerification.lean` (core Lean v4.31.0). PDF rebuilt: 63 pages, no
errors, zero missing-character warnings, no undefined references.

1. **Ariane 5 (Preface).** Rewritten. The concurrency claim was removed;
   replaced with the correct account (reused Ariane-4 alignment code, 64-bit
   float → 16-bit signed int overflow, unhandled Operand Error) framed as a
   caution against mis-citing non-concurrency bugs. Therac-25 kept (correct).

2. **λ→π encoding polarity (Ch 6).** Replaced with a correct monadic Milner
   call-by-name encoding: `⟦x⟧u = x̄⟨u⟩.0`, `⟦λx.M⟧u = u(x).u(w).⟦M⟧w`,
   `⟦M N⟧u = (νv)(⟦M⟧v ∥ v̄⟨n⟩.v̄⟨u⟩.0)`. Abstraction now INPUTS, application
   OUTPUTS (a "Polarity matters" warning box explains why the old both-inputs
   version was stuck). The polyadic tuples are gone (monadic throughout);
   the general replicated-server case is cited to Milner 1992. Verified: the
   `(λx.x) y` redex reduces in two `PiStep` steps in `PiCalcVerification.lean`
   (`idApp`, both steps proved by `PiStep.res PiStep.commR`).

3. **Scope-extrusion side condition (Ch 6).** Added `if a ∉ fn(Q)` to the
   reduction rule, with prose explaining the capture hazard and the tie-in to
   the Ch 7 structural-congruence version.

4. **Comm one-directionality (Def, l.676).** Added "and symmetrically…" plus a
   note that the Lean model makes both directions explicit (`comm`/`commR`).

5. **Deadlock prose (Ch 5).** Rewritten: the blocker is that both processes
   try to *send* first with no matching receiver ("two senders, no matching
   receivers"), not that they wait on inputs.

6. **CCS notation block (Ch 3).** Wrapped the four `scoped` declarations in
   `namespace CCSNotation … end` (matches the verification file). Also changed
   the notation glyphs `𝟎 ⬝ ∥` → `∅ ⊳ ‖` in BOTH book and Lean file, because
   `𝟎`(U+1D7CE), `⬝`(U+2B1D), `∥`(U+2225) are absent from DejaVu Sans Mono and
   rendered as tofu; the replacements are DejaVu-safe and still valid Lean
   notation (verified to compile).

7. **Capstone `worker` (Ch 12).** Changed to `partial def` and added
   `instance : Inhabited Pi := ⟨.nil⟩` first; added prose on the
   opaque-in-proofs trade-off and the contrast with structural `dispatcher`.

8. **Structural gap (π substitution + step relation).** ADDED to the book
   (new Definition "π-Calculus Substitution and Reduction" in Ch 6): a
   structural `Pi.subst` (capture-avoiding under the Barendregt convention) and
   an inductive `PiStep` reduction relation (`commL`/`commR`/`parL`/`parR`/
   `res`). Both compile in the verification file. Prose flags that the full
   relation also closes under structural congruence (omitted to stay
   computable by hand).

9. **Tactic primer / worked derivation (learning gap).** Added Appendix D
   "A Lean 4 Primer" (label `app:primer`) covering every construct/tactic the
   book uses — `inductive`, `def`/pattern matching, `structure`, `abbrev`,
   `Prop`/`theorem`/`example`, `instance`, `partial def`, `notation`/`infix`,
   `@[simp]`, `rfl`, `intro`/`exact`/`apply`, `refine`, `subst`, `simp`,
   `cases`, `induction … with`, `obtain`, `calc`, `Classical.byContradiction`,
   `do`, `sorry` — with the requested under-the-hood desugarings (`induction`
   ↔ `Tree.rec` shown as a term proof; `obtain` ↔ `match`/`Exists.elim`;
   `calc` ↔ `Trans.trans`; `by_contra` ↔ `Classical.byContradiction`; `do`
   ↔ `>>=`). Forward pointers added in the Preface, before the first tactic
   proof (`dual_dual`), and in Exercises 3.2/6.2. Every primer example is
   machine-checked in `PiCalcVerification.lean` (namespace `PiPrimer`).
   NOTE: `by_contra` is a *Mathlib* tactic, not core Lean, so — to keep the
   book genuinely zero-dependency — the primer shows only the core term form
   `Classical.byContradiction` and names `by_contra` as its Mathlib wrapper.

10. **Promise.race analogy (Ch 3).** Added a warning box: `+` discards the
    losing branch, `Promise.race` leaves losers running; `AbortController` is
    the closer match.

11. **HML `[τ]*` / `⋁_a` (Ch 8).** Added a warning box flagging both as
    outside the core grammar (Kleene star / infinite disjunction) and pointing
    to the modal μ-calculus.

12. **"Verified" oversell (Ch 12).** Added a warning box at the top of the
    capstone drawing the line between machine-checked (syntax, `dual_dual`, the
    two-step `CCSStep` and `PiStep` derivations) and proved-on-paper (the
    session/multiparty/worker-pool theorems).

13. **StructCong Lean subset (Ch 7).** Added prose noting the listing encodes
    only the CCS algebraic fragment and deliberately omits the four
    restriction/replication laws (and `resCong`) that the Definition headlines;
    extending to `Pi` flagged as an exercise.

14. **Comm math vs Lean (dup of 4).** Harmonized via the finding-4 edit.

15. **Appendix B index.** Completed: added `CCSAct.complement`, `philosopher`,
    `Pi.freeNames`, `Pi.subst`, `PiStep`, `BaseType`, `SessionType.dual_dual`,
    `Role`, `dispatcher`, `worker`.

- **D (version string).** The book printed no Lean version string; added the
  toolchain `leanprover/lean4:v4.31.0` to the Preface setup paragraph.
- **E (build).** Installed missing `epigraph` + `nextpage` TeX packages; pinned
  the full system DejaVu Sans Mono by path (as the sibling books do) and
  replaced the three non-DejaVu notation glyphs (see finding 6). Final build is
  clean at 63 pages.

### Verification file final state
`lake env lean pi-calculus/PiCalcVerification.lean` → exit 0, one `sorry`
warning only (Exercise 5.2, the book's own deadlock exercise; statement
type-checks). Added since the review: `Pi.subst`, `PiStep`, the `idApp`
two-step encoding reduction, and a `PiPrimer` namespace holding every
appendix-D example. Both original machine-checked derivations (`CCSStep`
request/response, `dual_dual`) still hold.

### Not previously flagged, fixed here
- Two literal `↔` (U+2194) in body prose (Ch "Looking Back") rendered as tofu
  in Latin Modern Roman; replaced with `$\leftrightarrow$`.
- Non-DejaVu notation glyphs `𝟎 ⬝ ∥` (see finding 6) — the review checked Lean
  compilation but not PDF glyph coverage; these would have printed as blanks.
