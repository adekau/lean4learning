# Proofreading review: from-zero-to-propagators.tex

Reviewed 2026-07-05 (full 3,859-line read; all ~46 Lean listings compiled and all
claimed runtime outputs executed against toolchain leanprover/lean4:v4.28.0, no
packages). Companion verification file: `PropagatorsVerification.lean` (compiles
clean, 0 sorries; every fix marked `-- DEVIATION:` with the book's error message).
Line numbers refer to the .tex.

## Verdict

The mathematical core (Part I: relations, posets, Hasse diagrams, lattices, M₃/N₅,
duality, distributivity, complete lattices, the paper Knaster–Tarski proof) is
essentially sound. The Lean code is not: roughly a third of the printed listings do
not compile, one listing contains a leftover LLM self-correction ("-- wait, we want
Prop, not Bool"), three claimed runtime outputs are wrong, and the Chapter 7 interval
example **loops forever** because its information order is inverted relative to the
book's own Chapter 5 convention. The printed chapters, the Selected Solutions, and
the pre-existing companion file use three different `PartialOrder` designs, so the
Solutions don't compile against the book's own class.

## Critical

1. **ll.2451–2675 — the interval chapter's order is upside-down; the flagship demo
   diverges.** `Interval.le` (l.2513–2515) makes `[l1,h1] ≤ [l2,h2]` iff
   `l2 ≤ l1 ∧ h1 ≤ h2`, i.e. narrower intervals are *lower* — directly contradicting
   the adjacent comment "narrower = more informative = higher" (l.2509), the Ch. 5
   convention (l.1939), and Ch. 8's candidate lattice. Join is therefore the widening
   hull, so `Cell.write`'s merge widens; with the forward propagator in
   `addConstraint`, the printed `#eval intervalExample` never quiesces (instrumented:
   after 100 passes the bounds have ~63 digits) instead of printing the claimed
   `y ∈ [2, 8]`. Tellingly, the companion `OrderAndLattices.lean` (ll.1128–1143)
   comments out the forward propagator to get the claimed answer. Also the defbox
   (ll.2451–2465) calls the contradiction element ⊥ (elsewhere contradiction is ⊤)
   and promises ℤ∪{±∞} while the code uses plain `Int`. Fix: flip the order (join =
   intersection, needs ±∞ for ⊥) or drop the forward propagator and say so honestly.
2. **ll.3286–3399 — type-inference capstone output wrong.** Claimed
   `true + 1 : TypeError`; actual output `true + 1 : Int`. The add propagator writes
   `.int` to the result cell unconditionally; the Bool⊔Int conflict stays in the
   operand cell. Fix (verified): write `Ty.unify` of the re-read operand types to
   the output cell.
3. **ll.2341–2346, 2417–2419, 3807–3827 — conflict propagation claims false.**
   Ch. 6's `addProp` matches `| _, _ => return false`, silently swallowing
   `conflict` inputs, so it is *not* "addFn wrapped in IO" and conflicts do not
   propagate; the printed Solution 6.2 prints "sum unknown", not the claimed
   "sum is conflict". Fix: `csum.write (FlatNat.addFn x y)` (as the companion file
   already does).
4. **ll.1156–1160 — wrong #eval output.** `iterToFixpoint double12 1 10` is annotated
   `-- [1, 2, 4, 12]` and the prose says the chain reaches 12; actual output is
   `[1, 2, 4]` (8 ∉ D12, so 4 is a fixed point).

## Lean compile errors (all reproduced; fixes in PropagatorsVerification.lean)

5. **ll.395–402** — the Nat `PartialOrder` instance specifies `le` twice, with the
   leftover self-correction comment "`le := Nat.ble  -- wait, we want Prop, not
   Bool`". Delete the first line and the comment.
6. **ll.3205–3237** — none of the `Ty` order-instance proofs compile (`induction t1
   <;> cases t2` produces mismatched IHs; the named `case fun_.fun_ ...` doesn't
   bind; `≤` never unfolds; `tauto` doesn't exist in core). Reproved as standalone
   structural-induction lemmas.
7. **ll.2946–3093 — Sudoku code, six distinct failures**: dead ill-typed `removed`
   binding (l.2968); every `for i in [:9] ... by omega` fails (needs
   `for h : i in [:9]` + `h.upper`); `rows[r.val]![c.val]!` needs an `Inhabited
   (Cell CandidateSet)` (IO.Ref has none); `cases hi : t.present i` after `cases t`
   (unknown identifier); h1/h2 swapped in the antisymmetry proof; seeding
   `⟨d - 1, by omega⟩` unprovable for arbitrary `d` (needs a dependent if). After
   fixes the solver works and fully solves the example puzzle by propagation alone.
8. **ll.2246–2339 (FlatNat) and ll.2540–2571 (Interval)** — the `simp
   [OrderBook.PartialOrder.le]` idiom fails everywhere ("simp made no progress":
   simp can't unfold `≤` through the instance projections when `le` is an anonymous
   match); `sup_le` for FlatNat is missing its final `m = n` case split entirely;
   the add/sub propagator monotonicity proofs need `split <;> simp_all`; Interval's
   `DecidableEq` has a trailing `exact` after `congr 1` already closed the goal
   ("No goals to be solved"). Fixed via named `le` defs + `le_def` rfl-lemmas.
9. **ll.1744–1769 — Knaster–Tarski Lean proof** passes proofs where the class's
   explicit element arguments go, and uses nonexistent `le_of_eq`. (The paper proof
   at ll.1720–1736 is correct.)
10. **Other verified compile failures**: DvdNat instance (ll.577–607: missing `le`
    field, `rename_i` grabs the wrong hypotheses, spurious `.symm`); Dual
    PartialOrder (ll.1317–1324: missing `le` field, wrong binder style, explicit
    args); `Lattice Bool` (ll.1377–1378: core `Bool.le_antisymm/le_trans` take
    elements implicitly — eta-expand); `mul_eq_one_left` (ll.501–528: `calc` with
    `≥` has no `Trans` instance in core; also its comment "No omega" is contradicted
    by its own final `omega`); `inferExpr` (ll.3291–3327: `(· .push do ...)` — the
    space after `·` misparses; must be `(·.push ...)`); Selected Solutions
    (ll.3597–3718: written against a different `PartialOrder` design than the book's
    own class — redundant `[LE α]` binders create a second unrelated `≤`, missing
    `le` fields, missing explicit args).

## Math/content errors

11. **ll.2776–2787 — Sudoku elimination worked example is impossible**: the union of
    the given row/column/box sets is all nine digits, leaving ∅ (not one candidate),
    and the displayed formula "{5} \ {5} ∪ …" is gibberish. Remove 5 and 9 from the
    box set to make the example work.
12. **ll.2729–2734 — Sudoku figure**: several grey "solved" digits contradict the
    puzzle's unique solution (verified by running the fixed solver), and row 3 shows
    a duplicate 9 in one row.
13. **ll.1849–1859 — ACC example**: "the only strictly ascending chains are
    ⊥ < known(n), length 2" — false; ⊥ < known n < conflict has length 3 (the
    "at most two updates" conclusion survives). Same box uses FlatNat and the
    interval lattice two chapters before they exist, with no forward reference.
14. **l.3461** — "`#check Prop -- Prop : Sort 0`": actual output is `Prop : Type`.
15. **l.3514** — the Appendix tactics table lists `tauto`, which doesn't exist in
    core Lean 4 (Mathlib-only), contradicting the zero-dependency premise.
16. **ll.922–923** — the bounds figure draws a non-cover Hasse edge a–c (violates
    the convention defined at l.660). **l.417** cites a "previous section" discussion
    that doesn't exist. **l.2290** has raw LaTeX inside `\mintinline`. **ll.1563–1570**
    (Ex 3.1): disjoint intervals have no meet in the given order (no empty interval),
    so the exercise's premise silently fails.

## Learning gaps (audience: SWE, minimal higher math / no Lean)

17. Tactics/idioms used but never introduced and absent from the Appendix table:
    `obtain`, `rename_i`, `by_cases`, `exfalso`, `subst`, `calc`, `split`, `change`,
    `rcases`, `Id.run`, `partial def`, and `do` with `mut`/`for`/`while`. The Ch. 1
    antisymmetry proof and the Ch. 8–9 imperative code are cliffs; a half-page on
    `do`/`mut`/`Id.run` before Ch. 8 plus the missing table rows would close most
    of the gap.

## Verification summary

- 100% of the book's printed Lean listings verified in
  `PropagatorsVerification.lean` (1,420 lines): `lake env lean` → exit 0, 0 errors,
  0 warnings, 0 sorries.
- Runtime outputs confirmed **correct**: sup/inf evals, printHasse, isMonotone,
  fixedPoints, iterToFixpoint (from 3 and 12), exampleNetwork (y = 7), mulNetwork
  (y = 4), conflictExample, the (fixed) Sudoku solver's full solution, type-inference
  examples 1–3, `#check Nat/Type`.
- Runtime outputs confirmed **wrong**: items 1–4 and 14 above.
- Pre-existing `OrderAndLattices.lean` compiles cleanly but covers only Chs. 1–7,
  in a different class architecture, with the interval forward propagator commented
  out (corroborating item 1). Left untouched.
- Not verified: TikZ figure rendering (checked by reasoning about coordinates only)
  and the LaTeX build itself.

## Resolution (2026-07-05)

All findings resolved in `from-zero-to-propagators.tex`;
`PropagatorsVerification.lean` rewritten to mirror the corrected book
(compiles clean: 0 errors, 0 warnings, 0 sorries; every `#eval` output
matches what the book now prints). PDF rebuilds with 0 errors and 0
missing-glyph warnings (117 pages).

### Critical

1. **Interval chapter redesigned** (Ch. 7). Carrier is now
   `Interval = range (lo hi : Option Int) (ok : ordered lo hi) | empty`,
   where `none` encodes an unbounded end (±∞). Information order flipped to
   match Ch. 5: narrower = higher; join = **intersection**
   (`loMax`/`hiMin`, collapsing to `empty` on crossed bounds);
   ⊥ = `unbounded` = (−∞,+∞); ⊤ = `empty` = contradiction (defbox and
   figure redrawn accordingly — contradiction is now TOP, matching
   FlatNat/CandidateSet). The `range` proof field makes crossed pairs
   unrepresentable, which is exactly what rescues the `sup_le` law
   (`ordered_squeeze`). All lattice-instance proofs rebuilt on a dozen
   bound-level lemmas; `add`/`sub` handle unbounded ends
   (`addBound`/`subBound` + `ordered_*` lemmas). `intervalExample` now runs
   with forward AND backward propagators, quiesces (pass-2 fixpoint,
   traced in a notebox), and its printed output is run-verified:
   `x ∈ [2, 8] / y ∈ [2, 8] / sum ∈ [10, 10]`. Old `Interval.intersect`
   deleted (the join IS intersection); Exercise 7.1 replaced by
   "the hull is the meet"; a "Termination, honestly" notebox explains that
   the lattice fails the ACC and why this system terminates anyway.
2. **Type-inference add propagator fixed**: it now re-reads the operand
   cells after constraining them to `.int` and writes `Ty.unify t1 t2` to
   the output, so `true + 1 : TypeError` — run-verified.
3. **Ch. 6 `addProp`/`subProp` now wrap the pure `addFn`/`subFn`**
   (`csum.write (FlatNat.addFn x y)`), so conflicts propagate; §6.4's
   "wrapped in IO" claim and the load-bearing bullet are now true, and
   Solution 6.2's `conflictPropagates` prints "sum is conflict (expected)"
   — run-verified. `exampleNetwork` still prints `y = 7`.
4. **`iterToFixpoint double12 1 10`** annotation corrected to `[1, 2, 4]`
   and the surrounding prose now explains 8 ∉ D12 (so 4 is a fixed point)
   and points at the 3 → 6 → 12 chain for a run that reaches the top.

### Compile errors

5. Nat instance: duplicate `le` + "wait, we want Prop, not Bool" leftover
   deleted.
6. `Ty` order laws reproved as standalone structural-induction lemmas
   (`Ty.le_refl_thm` …) plugged into the instances as terms; prose explains
   why the recursive `fun_` constructor forces this; `tauto` gone.
7. Sudoku: all six failures fixed as in the verification file
   (`for h : i in [:9]` + `h.upper` everywhere; dead `removed` binding
   deleted; `makeGrid` dummy-cell `Inhabited` instance; `le_antisymm`
   rewritten with `rename_i sp tp` and correct h1/h2; dependent
   `if h : 1 ≤ d ∧ d ≤ 9` seeding; `Bool.and_eq_true _ _ ▸`). The solver's
   run-verified full solution is now printed in the book.
8. FlatNat/Interval simp-unfolding: order given a name (`FlatNat.le`) plus
   rfl-lemma `le_def`; missing `sup_le` known/known case added;
   `subPropagator` uses `split <;> simp_all`; Interval `DecidableEq`
   rewritten for the new carrier (no trailing `exact`).
9. Knaster–Tarski: explicit element arguments supplied to
   `le_trans`/`le_antisymm`; `le_of_eq` replaced by `rw [hx]; exact
   le_refl x`; comment added.
10. DvdNat instance (le field, `obtain` inside the tactic block, no
    `.symm`), Dual PartialOrder (le field, explicit binders/args), Lattice
    Bool (eta-expansion), `mul_eq_one_left` (calc flipped to ≤, "No omega"
    comment corrected), `(·.push …)` spacing fixed in all four inferExpr
    propagators + prose warning, Selected Solutions rewritten against the
    book's own PartialOrder class (no `[LE _]` binders; explicit args in
    Ex 3.4; Ex 3.1 flipped to the information order with a meet/join
    discussion; solutions preamble states the `open OrderBook` convention,
    also added as a Ch. 1 notebox).

### Math/content

11. Elimination example: box set changed to {1,2,6,9} so exactly {5}
    remains; display formula rewritten as a single set difference.
12. Sudoku figure: wrong given 7/6/6 corrected to 7/8/6 (was a duplicate 9
    row); all grey digits replaced with values from the solver's verified
    unique solution.
13. ACC box: chain ⊥ < known(n) < conflict, length 3 ("at most two updates"
    kept); forward references to Ch. 6 (FlatNat) and Ch. 7 (intervals)
    added; interval non-ACC example rewritten for the corrected order
    ((−∞,∞) < [0,∞) < [1,∞) < ⋯). Ch. 5's "domain lattice is always
    finite" claim also repaired (Ty is not finite).
14. `#check Prop` annotation corrected to `Prop : Type`.
15. `tauto` row removed; the appendix table now lists exactly the tactics
    the book uses (26 rows + `<;>` and bullets).
16. Non-cover Hasse edge a–c removed from the bounds figure; l. 417
    phantom "previous section" reference reworded; raw `\not\leq` inside
    `\mintinline` rewritten as prose + math; Ex 3.1 premise fixed (see 10).

### Learning gaps

17. Appendix expanded into "Lean 4 Quick Reference and Tactic Primer"
    (labels `app:quickref`/`app:primer`): entries with worked, compiled
    examples for intro/exact, apply, rfl, constructor, cases (+ `Bool.rec`
    desugaring), induction (+ explicit `Nat.rec` term), obtain/rcases
    (+ `Exists.elim` and `match` desugarings), rename_i, by_cases
    (+ dependent-if desugaring), exfalso, subst, calc (+ `Trans.trans`),
    split, change, simp/simp_all/simp only, omega, decide, have/show,
    funext/congr; plus a Programming Constructs section
    (do/mut/for/while desugaring to folds, `Id.run`, `IO.Ref`,
    `partial def`, structures/classes/deriving). A half-page
    "Interlude: Imperative Lean in Half a Page" added at the top of the
    first imperative chapter (Ch. 6) with a run-verified example, and a
    forward-pointer notebox added at the book's first tactic proof
    (Ch. 1). All primer examples live in §P of
    `PropagatorsVerification.lean` and compile.

### Additional fixes beyond the review

- Preamble: `unicode-math` moved after `amssymb` (kills the 4 cold-build
  "already defined" errors); section title with math moved to plain text
  (was breaking hyperref bookmarks).
- The TeX-distribution copy of DejaVu Sans Mono is trimmed and lacks
  ⊓/⊔ — every lattice-notation glyph in every code listing was silently
  dropped in the old PDF (62 missing-character warnings). The preamble now
  loads the full system font files explicitly; 0 missing characters remain.
  Comment glyphs with no mono coverage anywhere (⨆, ⨅, ∤) were rewritten
  as ASCII-safe text in book + verification file.
- `\checkmark` in a TikZ node wrapped in math mode (was a missing glyph).
- `def myList … := ...` ellipsis placeholder in the appendix given a real
  body (`Fin n → α`).

## Toolchain note (2026-07-05, post-resolution)

Repo `lean-toolchain` bumped v4.28.0 → v4.31.0; `PropagatorsVerification.lean` and
`OrderAndLattices.lean` both re-verified on v4.31.0 with no changes needed
(0 errors / 0 warnings / 0 sorries). The book remains zero-dependency core Lean.
