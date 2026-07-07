# Proofreading review: galois-theory-for-programmers.tex

Reviewed 2026-07-06 (full 2,397-line read; every Lean listing and every checkable
prose claim extracted and compiled against toolchain leanprover/lean4:v4.31.0, core
Lean only — no packages — as the book advertises). Companion verification file:
`GaloisVerification.lean` (compiles clean; 3 sorries, all book-intended; every fix
marked `-- DEVIATION:` with the book's error, every book-left sorry marked
`BOOK'S OWN SORRY`). Line numbers refer to the .tex. This is review only — the .tex
was not edited.

## Verdict

The prose mathematics is, for a change, largely sound: the group/ring/field
definitions, Lagrange's theorem and its Euler/Fermat corollaries, the tower law, the
fundamental theorem of Galois theory (stated correctly, **with the inclusion reversal
in the right direction** and correct degree/index and normal-subgroup clauses), the
S₄-solvable / A₅-simple / S₅-unsolvable chain (conjugacy-class arithmetic checked),
the finite-field classification, and the constructibility impossibility proofs
(cos 20° minimal polynomial re-derived) are all correct. Two genuine math defects
stand out: (1) the **S₃ multiplication table is non-associative** — it is not a group
at all, and it silently breaks three exercises; and (2) the **Chapter 3 Galois-
connection definition is the *monotone* one, yet the text insists it is *antitone*
and derives order-reversal that does not follow** — the proof even contains a leftover
"Wait—this proves…" self-correction. The Lean side repeats the pattern of the other
books in this repo: the "vanilla Lean 4, no Mathlib" promise (l.275) is false for the
book's own code — `Set`, `Inf`, `Sup`, and the `ring` tactic are all Mathlib-only —
and several listings do not compile as printed (wrong `Int` lemma names, a failing
`omega`, a failing termination proof, undefined `embed`). None of the deviations are
unfixable; the corrected, fully compiling versions are in the companion file.

## Math errors

1. **ll.513–540 — the S₃ multiplication table is not associative; it is not a group.**
   Executed exhaustively over all 6³ = 216 triples: associativity `#eval` returns
   `false`. Eight products are wrong (verified by comparison against the composition
   table forced by the book's own reflection labelling — s, sr, sr2 fixing vertices
   1, 3, 2, with the entries r·s = sr and r2·s = sr2 that the book already gets
   right):
   `r·sr` book `s`→`sr2`; `r·sr2` `sr`→`s`; `r2·sr` `sr2`→`s`; `r2·sr2` `s`→`sr`;
   `s·sr` `r`→`r2`; `s·sr2` `r2`→`r`; `sr·s` `r2`→`r`; `sr2·s` `r`→`r2`.
   Consequence: Exercise 1.2 ("prove associativity … by `decide`", l.564) is
   **impossible** with the printed table — `decide` would report the operation is
   non-associative; likewise the subgroup enumeration in Exercise 2.1 rests on a
   non-group. The prose non-abelian claim at l.554 (`r·s = sr`, `s·r = sr2`) happens
   to use two entries that *are* correct, so that illustration survives. Fix: the
   corrected, associativity-verified table in `GaloisVerification.lean` §Ch1 (the four
   rotation·rotation entries and the r·s / s·r entries are unchanged).

2. **ll.1018–1080 — Galois-connection definition is monotone but claimed antitone.**
   Definition 3.x (l.1023) and the Lean structure (l.1035) both state
   `ℓ(p) ≤ q ⟺ p ≤ u(q)`. That is the standard **monotone** (order-*preserving*)
   Galois connection: under it both ℓ and u are monotone. But Proposition 3.x(i)
   (l.1056) asserts "Both ℓ and u are order-**reversing**", the Warning (l.1074) says
   "We follow the antitone convention", and Chapter 8 needs the antitone version
   (bigger field ↔ smaller group). Under the definition as written, Prop 3.x(i) is
   false. The antitone correspondence needs the *other* adjunction, e.g.
   `q ≤_Q ℓ(p) ⟺ p ≤_P u(q)`. The proof at ll.1065–1072 visibly notices the trouble
   ("Wait---this proves ℓ is order-reversing only if the Galois connection is
   antitone"). Fix: either give the antitone adjunction `q ≤ ℓ(p) ⟺ p ≤ u(q)`
   (and prove antitone), or keep the monotone definition and state that ℓ, u are
   monotone — but then reconcile with the Ch. 8 reversal (which is genuinely antitone
   because Fix/Inv reverse inclusion).

3. **ll.1764–1811 — the Chapter 9 (x⁴−2) twin-lattice figures are garbled.** The
   field side draws `E` and `Q(⁴√2,i)` as two distinct nodes although
   `E = Q(⁴√2, i)` is exactly the splitting field defined one page earlier (l.1725);
   it also shows only 9 field nodes for the 10 intermediate fields the text just
   promised (l.1761). The subgroup side lists `⟨ρ²⟩` **twice** (nodes at −1.5 and −3)
   and shows only 3 of the 5 order-2 subgroups of D₄ (the genuine ones are
   `⟨ρ²⟩, ⟨τ⟩, ⟨ρτ⟩, ⟨ρ²τ⟩, ⟨ρ³τ⟩`). The count "D₄ has 10 subgroups … exactly 10
   intermediate fields" (l.1761) is itself correct (1 + 5 + 3 + 1 = 10); only the
   diagrams are wrong. Fix: redraw both Hasse diagrams with the correct 10 nodes each
   and the E = Q(⁴√2,i) identification.

## Lean errors (all reproduced with the compiler; fixes in GaloisVerification.lean)

4. **Systemic — the "no Mathlib" promise (l.275) is false for the book's own code.**
   `Set` (l.694, l.1648, l.1654), `Inf`/`Sup` (ll.981–982), and the `ring` tactic
   (ll.1530, 1535, 1540) are all Mathlib-only; each produces a hard error in core
   Lean v4.31.0. Either declare Mathlib a dependency or port these (the verification
   file ports every one to core Lean, so it is feasible).

5. **ll.417–418 — the ℤ group instance uses two nonexistent lemmas.**
   `inv_mul := Int.neg_add_cancel` and `mul_inv := Int.add_neg_cancel` both give
   "Unknown constant". The correct core names are `Int.add_left_neg` and
   `Int.add_right_neg`. Confirming this is broken: the user's own `Galois.lean`
   (ll.22–23) already substitutes exactly those two names.

6. **ll.448–450 — `Fin.addMod` does not compile.** `Nat.mod_lt _ (by omega)` fails:
   `omega` reports "No usable constraints found" because nothing in scope proves
   `0 < n`. Fix: derive `0 < n` from the input `a : Fin n` via `a.isLt`. (The sibling
   `Fin.negMod` at l.451 compiles, because it takes `h : n > 0` explicitly.)

7. **l.639 — `GroupHom.map_one`'s scaffold does not compile.** The body
   `simp [mul_one] at h` errors with "Unknown identifier `mul_one`" (it is
   `Group.mul_one`); because that line precedes the `sorry`, the whole listing fails.
   The statement is a deliberate exercise (1.4), so the fix is just to correct/remove
   the scaffold line and keep the `sorry`.

8. **ll.1530, 1535, 1540 — the three `conjugate_*` theorems end in `ring`.** `ring`
   is not a core tactic ("unknown tactic"). `conjugate_conjugate` and
   `conjugate_fixes_rat` close with plain `simp [conjugate]` (drop `; ring`);
   `conjugate_mul` needs its two ℚ-components discharged with core `Rat.mul_neg`,
   `Rat.neg_mul`, `Rat.neg_neg`, `Rat.neg_add` (done in the verification file).

9. **ll.1487–1496 — `FieldAut` does not compile.** Two independent problems: (a) it
   writes `toFun (a + b)` and `toFun (a * b)`, but the book's `Field` class exposes
   no `Add`/`Mul` instance on the carrier, so `failed to synthesize HAdd E E E` /
   `HMul E E E`; (b) `fixes_base` references `embed`, which is never defined
   ("Function expected at embed"). A compiling shape (Add/Mul instances + explicit
   embedding) is in the verification file.

10. **ll.2055–2067 — `GF256.mul` fails its termination proof** (the Chapter 12
    capstone). With `if b == 0` and only `termination_by b.toNat`, Lean cannot show
    `(b >>> 1).toNat < b.toNat` and reports "failed to prove termination". Fix: use
    `if h : b == 0` to obtain `b ≠ 0`, then a `decreasing_by` block rewriting
    `(b >>> 1).toNat = b.toNat / 2` (`UInt8.toNat_shiftRight`,
    `Nat.shiftRight_eq_div_pow`) and closing with `omega`. Fixed version compiles and
    the standard AES test vector **0x57 · 0x13 = 0xFE** checks (as does
    `0x53 · 0x53⁻¹ = 1`).

11. **ll.1647–1662, 1860–1867 — the Chapter 8 correspondence skeleton and
    `IsSolvable` reference undefined names.** `Gal E F`, `IntermediateField`, `Inv`
    (l.1661 mixes the prose name `Inv` with the Lean name `fixingGroup`, and `Inv` is
    never defined in Lean), `IsNormal`, `IsAbelian`, and a two-argument `Quotient`
    (l.1866) do not exist. These blocks are schematic prose-in-code that all end in
    `sorry`; they are not meant to type-check, but a reader who pastes them gets a
    wall of "unknown identifier". Worth a one-line "the following is illustrative and
    does not compile" caption.

## Learning gaps (SWE with minimal higher math)

12. **No tactic/Lean primer.** Prerequisites (l.271) name only
    `intro`/`rfl`/`simp`/`omega`/`cases`/`induction`, yet the listings use
    `native_decide`, `decide`, `deriving`, `termination_by`, `where`, structure/class
    extension, and (nominally) `ring` — none introduced. The book's only appendix
    (l.2360) is the typeclass hierarchy. The sibling books in this repo each grew a
    "Lean 4 Quick Reference and Tactic Primer" appendix; this one needs the same,
    plus a note that `native_decide` trusts the compiler and `decide` can be slow on
    216-case goals.

13. **The two deepest theorems are asserted, never proved.** The Fundamental Theorem
    (Ch. 8) and Galois's solvability criterion (Ch. 10) appear only as statements
    plus `sorry` skeletons. That is fine for the book's stated scope, but a beginner
    should be told explicitly "we take these on faith; proving them is beyond a
    from-scratch core-Lean development" rather than being handed non-compiling code.

14. **Separability is defined (l.1551) but its char-0 triviality is never mentioned.**
    Every example field is ℚ or a subfield of ℂ, where all extensions are
    automatically separable, so the reader never sees *why* the hypothesis is real.
    One sentence ("over ℚ separability is automatic; it only bites in characteristic
    p") would close the gap, especially before the finite-field chapter where it
    matters.

15. **Broken exercises give no feedback.** Exercises 1.2, 1.3, and 2.1 all build on
    the non-associative S₃ table (finding 1); a diligent reader will be unable to
    complete them and will assume the fault is theirs.

## Internal inconsistencies (minor)

16. **`Fix`/`Inv` naming is nonstandard and clashes with the Lean code.** Prose
    (l.1617) uses `Fix(K) = Gal(E/K)` for the field→group map, but conventionally
    "Fix" denotes the *fixed field* (group→field); the Lean code (ll.1647, 1653)
    correctly names them `fixedField` (group→field) and `fixingGroup` (field→group),
    i.e. the standard way — so prose `Fix` = Lean `fixingGroup`, which will confuse a
    reader cross-referencing any other source. Pick one naming and use it in both.

17. **modPow (l.599)** is correct (repeated-squaring, right-to-left); the book gives
    no explicit `#eval` output to check, but `3^4 mod 7 = 4`, `2^10 mod 1000 = 24`,
    `7^13 mod 11 = 2` all verify — no error, noted for completeness.

## Verification summary

- **Coverage:** every Lean listing in the book was extracted and compiled — Ch. 1
  (Group class, ℤ instance, Fin addMod/negMod, S₃, modPow, GroupHom), Ch. 2
  (Subgroup, NormalSubgroup), Ch. 3 (PartialOrder, Lattice, GaloisConnection), Ch. 4
  (Ring, Field), Ch. 5 (Polynomial), Ch. 6 (QSqrt2), Ch. 7 (conjugate + FieldAut),
  Ch. 12 (GF256). The purely schematic sorry-skeletons (Ch. 8 correspondence, Ch. 10
  `IsSolvable`) are documented but not reproduced (they reference a dozen undefined
  names by design). ~15 of ~15 compilable listings verified; 2 schematic blocks
  documented.
- **File:** `/home/adekau/lean4learning/galois/GaloisVerification.lean`.
- **Final compile:** `lake env lean galois/GaloisVerification.lean` → **0 errors**,
  3 `sorry` warnings (all book-intended) + 1 benign unused-binder linter warning.
- **Deviations applied (each marked in-file):** Int lemma names (5); Fin.addMod
  positivity (6); S₃ table — 8 entries (1); GroupHom.map_one scaffold (7); `Set`
  supplied as `α → Prop` (4); `Inf`/`Sup` instances dropped (4/6); three `ring`→core
  rewrites (8); FieldAut given Add/Mul + explicit embed (9); GF256 termination via
  `decreasing_by` (10).
- **Book-intended sorries reproduced:** `GroupHom.map_one`, `GroupHom.map_inv`
  (Exercise 1.4); `GF256.sbox.affineTransform` (book's `sorry`, l.2092). = 3 total.
- **Outputs confirmed:** `QSqrt2.mul sqrt2 sqrt2 = ⟨2,0⟩` (√2·√2 = 2) ✓;
  `GF256` AES vector `0x57·0x13 = 0xFE` ✓ and `0x53·0x53⁻¹ = 1` ✓; S₃ corrected table
  associative + inverses correct ✓; modPow values ✓.
- **Outputs wrong:** none claimed in the book turned out numerically wrong; the S₃
  table is a *code* error (non-associative), not a printed-output error.

## Coverage

Full sequential read of all 2,397 lines. Every chapter's mathematics re-derived where
a specific computation was claimed (S₃ Cayley table, D₄ subgroup/field counts, A₅
conjugacy-class arithmetic, cos 20° minimal polynomial and its rational-root check,
tower-law degrees, Euler/Fermat corollaries). Every Lean listing compiled on
v4.31.0 core Lean; every fix and every book-intended sorry recorded in
`GaloisVerification.lean`. Compared against the user's `Galois.lean`, which
independently confirms finding 5 (the ℤ-instance lemma-name fix).

## Resolution (2026-07-06)

All findings fixed in place. The book was patched surgically; the two rewrites
(S₃ table, Ch. 9 twin lattices) and the Ch. 3 antitone reframing are the only
large edits. Verification file kept in sync and compiling. PDF rebuilt clean.

**Mathlib decision (Task B): PORTED to core Lean.** The entire Mathlib footprint
was three shallow touchpoints — `Set`, `Inf`/`Sup`, and `ring` — each replaceable
in a few lines, and `GaloisVerification.lean` already demonstrated a full compiling
core-Lean port. Porting keeps the book's "vanilla Lean 4, no Mathlib" brand
*true* rather than retracting it, so the single core-Lean witness file was kept
and **no** `GaloisMathlibVerification.lean` was created.

Finding-by-finding:

1. **S₃ table** — replaced the 8 wrong products with the associativity-verified
   table (§Ch1 of the verification file). Prose non-abelian illustration
   (`r·s=sr`, `s·r=sr2`) still holds. Exercises 1.2/1.3/2.1 now succeed.
   Associativity + inverses re-checked exhaustively by `native_decide` in the
   verification file.
2. **Ch. 3 Galois connection** — flipped the definition to the antitone
   adjunction `q ≤ ℓ(p) ⟺ p ≤ u(q)` (def, Lean structure, and Def title now say
   "antitone"). Proposition rewritten: (i) both maps order-reversing, (ii)/(iii)
   the two extensivity/unit inequalities, (iv) idempotence — with a correct proof
   and the "Wait—…" self-correction removed. Warning kept (already antitone).
   Verification file gains four proved lemmas (`le_u_l`, `le_l_u`, `l_antitone`,
   `u_antitone`).
3. **Ch. 9 twin lattices** — both Hasse diagrams redrawn from scratch: field side
   now shows all 10 intermediate fields with `E = Q(⁴√2,i)` as one node; subgroup
   side shows the correct 10 subgroups (all five order-2 groups
   `⟨ρ²⟩,⟨τ⟩,⟨ρ²τ⟩,⟨ρτ⟩,⟨ρ³τ⟩`, no duplicate `⟨ρ²⟩`), drawn upside-down so
   vertically-aligned pairs are the correspondence; an explicit pairing list added
   below. Verified visually in the built PDF (fits the text block).
4. **No-Mathlib port** — `Set` now defined in-book as `abbrev Set α := α → Prop`
   plus a `Membership` instance (Ch. 2); `Inf`/`Sup` instances dropped with a note;
   `ring` replaced by core proofs (see 8). Preface l.275 claim kept but made
   explicit/honest (names toolchain v4.31.0, "core library only", says we roll our
   own `Set`).
5. **ℤ instance** — `Int.add_left_neg` / `Int.add_right_neg`.
6. **Fin.addMod** — positivity now derived from `a.isLt` via
   `Nat.lt_of_le_of_lt (Nat.zero_le _) a.isLt`.
7. **GroupHom.map_one scaffold** — dropped the erroring `simp [mul_one] at h`
   line; kept the informative `have h := φ.map_mul 1 1` and the `sorry` (Ex 1.4).
8. **conjugate_* / ring** — `conjugate_conjugate` and `conjugate_fixes_rat` close
   with `simp [conjugate]`; `conjugate_mul` uses core `Rat.mul_neg`/`neg_mul`/
   `neg_neg`/`neg_add`. Added a note that Mathlib's `ring` would do it in one line.
9. **FieldAut** — added `Add`/`Mul`/`Zero`/`One`/`Neg` notation instances for
   `Ring` (Ch. 4, mirroring the Ch. 1 Group notation) so `+`/`*` synthesize, and
   made `embed : F → E` an explicit field. Now type-checks.
10. **GF256.mul termination** — `if h : b == 0` + a `decreasing_by` block rewriting
    `(b >>> 1).toNat = b.toNat / 2` and closing with `omega`. Added in-book AES
    sanity checks `0x57·0x13 = 0xFE` and `0x53·0x53⁻¹ = 1` (both `native_decide`).
11. **Ch. 8 / Ch. 10 schematic blocks** — each leanbox now carries an
    "ILLUSTRATIVE ONLY (does not type-check)" caption; the undefined `Inv` in
    `galois_connection` replaced by `fixedField`, with the adjunction restated in
    the antitone direction consistent with Def 3.x.
12. **Tactic primer** — new numbered Appendix A "A Lean 4 Primer" covering
    inductive/def/structure/class/instance/extends/deriving, theorem/example/Prop,
    rfl/intro/exact/apply/rw/simp, decide vs native_decide (with the trust/speed
    note), omega, cases (↔ `T.rec`), induction (↔ `Nat.rec`), obtain (↔
    `Exists.elim`), calc (↔ `Trans.trans`), by_contra (↔ `Classical.byContradiction`,
    flagged non-core), where, termination_by/decreasing_by, ring (flagged Mathlib),
    and sorry. Every example machine-checked in the verification file's `Primer`
    namespace. Forward pointers added in the Preface and at the first listing.
13. **Deep theorems asserted** — Warning boxes added after the Fundamental Theorem
    (Ch. 8) and Galois's Criterion (Ch. 10) stating plainly that these are taken on
    faith and the Lean blocks are honest skeletons, not from-scratch proofs.
14. **Char-0 separability** — Intuition box added after the separable-extension
    definition explaining that separability is automatic in characteristic 0 and
    only bites in char p (forward ref to the finite-field chapter).
15. **Broken exercises** — resolved transitively by finding 1 (the S₃ table is now
    a genuine group).
16. **Fix/Inv naming** — prose now uses the standard, Lean-matching names
    `fixingGroup` (field→group) and `fixedField` (group→field) via new `\fixgrp` /
    `\fixfld` macros, throughout the FTGT statement, the tikzcd/figure labels, the
    Ch. 8 skeleton, and Ch. 15.
17. **modPow** — correct; no change.

**Verification file** (`galois/GaloisVerification.lean`, core Lean, v4.31.0):
`lake env lean galois/GaloisVerification.lean` → **0 errors**, **3 `sorry`
warnings** (`GroupHom.map_one`, `GroupHom.map_inv` = Ex 1.4; `GF256.affineTransform`)
+ 1 benign unused-binder linter warning on the `GF256` termination `h`. Added:
antitone GaloisConnection with four proved lemmas; Ring notation instances +
`FieldAut` with `embed`; a `Primer` namespace whose every example compiles.

**PDF build:** `latexmk -xelatex -shell-escape galois-theory-for-programmers.tex`
→ clean, exit 0, **62 pages**, 0 unresolved references, 0 missing glyphs. (Needed
`tlmgr install tikz-cd` once; pinned full system DejaVu mono by path in the
preamble.) Remaining overfull \hboxes (3) are all pre-existing long chapter
titles / wide code lines, not introduced here.

**Deferred:** none. All 17 findings addressed.
