# Proofreading review: verified-calculus-complete.tex

Reviewed 2026-07-05 (full 4,573-line read; all Lean code compiled against toolchain
leanprover/lean4:v4.28.0, no packages). Companion verification file:
`CalculusVerification.lean` (compiles clean; every fix marked `DEVIATION`, every
book-intended sorry marked `BOOK'S OWN SORRY`). Line numbers refer to the .tex.

## Verdict

The prose mathematics (Parts I–VI real analysis) is largely sound. The Lean content
is not: the book's central premise — "No Mathlib. No shortcuts." (l.200), "No external
mathematics libraries are imported" (Preface) — is false for its own code. From
Chapter 4 onward nearly every listing depends on Mathlib types (`Real`, `Finset`,
`List.Sorted`, `deriv`, `Real.exp`), Mathlib notation (`|·|`), and Mathlib tactics
(`linarith`, `nlinarith`, `positivity`, `norm_num`, `push_neg`, `by_contra`, `set`) —
none available in the toolchain the book claims to use. Only Chapter 2's code compiles
verbatim. Several capstone outputs are unobtainable from the printed code.

## Math errors (prose)

1. **l.3218 — Lagrange multipliers worked example.** Claims "maximum is f = 1/2 at
   (√2, 1/√2)". With constraint x²/4 + y² = 1 and f = xy, f(√2, 1/√2) = 1. The point
   is right; the value should be **1**. (Independently re-derived.)
2. **l.1575 — history remark.** "Cauchy claimed (incorrectly) that the uniform limit
   of continuous functions is continuous." The uniform-limit theorem is true; Cauchy's
   error concerned **pointwise** limits. The book states it correctly at ll.959 and
   2740 — an internal contradiction.
3. **l.1785 — connectedness definition.** "S is connected if it cannot be written as
   a disjoint union S = A ∪ B of two nonempty open sets" — with A, B open in ℝ this
   is wrong ([0,1] ∪ [2,3] would count as connected). The sets must be open **in the
   subspace topology** (or "separated"). The proof at l.1795 needs the same repair.
4. **l.1668** — the n-th-root corollary needs n ≥ 1.
   **l.2414** — U(f,P)/L(f,P) require f **bounded** (hypothesis omitted; the double-
   integral definition at l.3245 does include it).
   **l.4469** — "Risch ... always terminates ... decidable" overstates: by Richardson's
   theorem constant zero-equivalence is undecidable; Risch is an algorithm only modulo
   a constant-oracle.
   **l.758** — integral-domain definition omits commutativity and 1 ≠ 0.

## Lean errors (all reproduced with compiler output; fixes in CalculusVerification.lean)

5. **Systemic (title page l.200, Preface l.212, blocks at ll.918–937, 1101–1157,
   1314–1338, 1489–1512, 1598–1626, 1938–1966, 2063–2079, 2291–2305, 2443–2468,
   2556–2570, 2872–2892, 2948–2972, 3047–3063, 4426–4447).** Mathlib-only names and
   tactics throughout, despite the "No Mathlib" branding. Worse: the book constructs
   `MyReal` in Ch. 5, then silently abandons it — everything after uses Mathlib's
   `Real`, and the exercise at l.2493 even says "using Lean's `Real` type". Either
   declare Mathlib a dependency or port to core Lean (the verification file proves
   the ε-δ material over ℚ in core Lean, so it is feasible).
6. **ll.519–595 (Ch. 1).** The order/strong-induction/well-ordering block uses `<`,
   `≤`, `le_refl` on `MyNat` without ever defining LE/LT instances or order lemmas;
   `strong_ind` applies `Nat` lemmas to `MyNat`; `no_overflow`'s succ case needs
   `succ_add` in the simp set; `well_ordering` is structurally broken (goal `False`
   after by_contra, to which `strong_ind` cannot apply). Your own `Calculus.lean`
   contains exactly these repairs — the printed code never worked.
7. **ll.1148–1156.** `Quot.lift2` does not exist (core or Mathlib); binary lift also
   needs well-definedness in *both* arguments, only one proof supplied. Prose repeats
   the false claim at l.756.
8. **ll.3999–4110 (Ch. 33 integration engine).** Five compile-blockers: `substVar`/
   `substExpr`/`isInTermsOf` never defined; `innerFunctions` used before definition
   and its `| Pow u _ | Pow _ u` alternative rejected as redundant; `liatePriority`
   matches nonexistent constructors `Arctan`/`Arcsin`; `partialFracStrategy`/
   `trigReduceStrategy` referenced but left as exercises; the engine's mutual,
   non-structural recursion needs `mutual` + `partial def` (which also voids any
   termination claim).
9. **Capstone claimed outputs unobtainable (ll.4206–4217, 4359–4383, 4228–4229),
   demonstrated by #eval.** (a) `DiffStep.toTrace` threads the top-level result into
   every child, so the printed step traces are wrong; (b) `diff`'s `Pow` case discards
   the sub-trace, so the claimed Power-Rule trace cannot exist; (c) the flagship
   ∫ x·eˣ example fails: `liatePriority` gives bare `Var` priority 5 (below `Exp`),
   IBP picks the wrong u/dv, and the engine prints "no elementary antiderivative
   found". Even fixed, output is `x * exp(x) - exp(x)`, not `(x - 1)*exp(x)`.
10. **l.4426–4447 (`diff_correct`).** Unformalizable as printed: applies `deriv`
    (needs a normed field) to `Float → Float`, and the statement is false for Float
    rounding anyway. The honest version needs an `Expr` → (ℝ → ℝ) interpretation the
    book never defines. Ch. 36's "we can state and prove this formally" is unearned.
11. **Smaller as-printed failures (all verified):** `Real`-typed Newton with `#eval`
    (ll.2294–2304, `Real` noncomputable — should be `Float`); `ftc_part2` references
    an `integral` function never defined (ll.2560–2564); `Int.ofFloat` (l.3625)
    doesn't exist; `String.replicate` (l.4179) doesn't exist; `List.bind` (l.4183)
    is gone in v4.28 (`List.flatMap`); `toTrace` missing the `SubRule` case (l.4147);
    `Main.lean` uses `Mode` before declaring it (ll.4291–4297); pattern matches on
    bare `Add/Mul/Pow/Neg` without `open Expr`; Float-literal patterns in `simplify`
    (ll.3696–3729) rejected by dependent elimination; `midpoint` (l.873) uses
    `positivity`; `Partition.sorted` (l.2449) uses Mathlib-only `List.Sorted`;
    lakefile (l.4249) `name :=`/`version :=` fields rejected by modern lake, and
    binaries live under `.lake/build/bin/` not `./build/bin/` (ll.4241, 4353);
    `limit_unique` (ll.1321–1337) has unelaboratable `a _` placeholders;
    `sq_continuous_at` (l.1623) cites nonexistent `div_mul_lt_iff`; `const_deriv`
    (l.1950) rewrites `(c−c)/h` with `div_self` (inapplicable, numerator is 0);
    `Nat.not_dvd_iff_odd` (l.920) doesn't exist.

## Learning gaps (audience: SWE, minimal higher math / no Lean)

12. The book promises "No prior Lean 4 experience required" (l.214) but never
    introduces any Lean: Ch. 1 opens with `inductive`, `@[simp]`, instances,
    `induction ... with`, `rcases`/`obtain`, `calc`, `suffices`, all unexplained;
    Ch. 2 uses `Quot`/`Quot.lift`/`Quot.sound` with no account of the quotient API.
13. Concepts used but never defined: **limsup** (Cauchy–Hadamard, l.2813), metric
    spaces (ll.980, 1766); sin/cos/exp are used throughout with derivative proofs
    citing power series "proved" nowhere, despite the from-scratch promise; the
    MyReal → Real switch orphans the whole Part I construction.
14. l.3928's claim that strategy dispatch via `findSome?` "is a propagator network
    ... finds the least fixed point" is decorative nonsense (it's first-match
    short-circuiting). Ch. 36 cross-references companion books ("the lambda calculus
    book", "Galois theory book") the reader may not have.

## Internal inconsistencies (minor)

15. l.758 refers in past tense to a Chapter 3 proof from Chapter 2; l.4522 cites
    "multivariable optimisation chapters (Chs. 26, 27)" but Ch. 27 is Multiple
    Integrals; l.2551's FTC-2 calc chain has a tautological middle step; l.976
    "error halves quadratically" is self-contradictory; l.353's claim that
    second-argument recursion in `add` is forced by termination is wrong (it's
    convention).

## Verification summary

- ~90% of the book's Lean lines are represented in `CalculusVerification.lean`
  (1,470 lines); `lake env lean calculus/CalculusVerification.lean` → exit 0 with
  only the book's own 12 sorries as warnings.
- Not reproduced (documented in-file): Ch. 23 `partialDeriv`/`HasTotalDerivAt`
  (ill-typed even as sketches), Ch. 36 `diff_correct` (item 10).
- Existing `Calculus.lean` compiles but covers only Chapter 1, with proofs that
  differ substantially from the book's printed (broken) ones.
- Caveat: Mathlib is not installed here, so the `Real`-based tactic scripts were
  shown to fail in the environment the book claims to use; whether they would
  compile *with* Mathlib was not tested (several provably would not — items 9–11).

## Resolution (2026-07-05)

All findings above have been addressed in `verified-calculus-complete.tex`;
the book now builds clean (158 pp., no errors, no undefined references, no
missing glyphs). Companion verification:

- `CalculusVerification.lean` — Part I + capstone + Appendix A core examples;
  compiles on the repo toolchain (`lake env lean calculus/CalculusVerification.lean`,
  exit 0, only the book's own marked sorries).
- `CalculusMathlibVerification.lean` (NEW) — every Mathlib-dependent listing
  (Parts II–VII + Ch. 36 + Appendix A Mathlib tactics); compiles against
  Mathlib rev v4.31.0 / toolchain leanprover/lean4:v4.31.0 (exit 0, only the
  book's own marked sorries; `push_neg` deprecation warnings only), and also
  against Mathlib rev v4.28.0 (exit 0). Version
  strings printed in the book (lakefile, lean-toolchain) say v4.31.0 to match
  the repo's planned toolchain bump.

Per-finding disposition:

1. **Lagrange value (l.3218)** — corrected: maximum is $f=1$ at $(\sqrt2,1/\sqrt2)$;
   substitution steps spelled out.
2. **Cauchy uniform/pointwise (l.1575)** — corrected to *pointwise*; sentence added
   stating the uniform-limit theorem is the true statement. Now consistent with
   ll.959/2740.
3. **Connectedness (ll.1785, 1795)** — definition restated with subspace-open sets
   (incl. the $[0,1]\cup[2,3]$ example showing why relativisation matters); the
   continuous-image proof repaired to use subspace-open preimages.
4. **n-th roots** — now requires integer $n \ge 1$. **U/L sums** — boundedness
   hypothesis added to both defboxes and to the Lean sketch (plus an explicit
   `lowerSum`). **Risch** — Richardson-theorem caveat added in the historical
   note, the theorem box (decidable *modulo a zero-equivalence oracle*), and the
   closing remark. **Integral domain (l.758)** — now "commutative ring with
   1 ≠ 0"; tense fixed ("will be used ... in Chapter 3").
5. **Systemic Mathlib dependence** — resolved by decision A (keep Mathlib, make
   it explicit): title-page tagline rewritten; Preface rewritten as a two-phase
   plan naming both verification files; new §6.1 "From MyReal to Mathlib"
   (transition passage: MyReal explicitly retired, same-Cauchy-construction
   remark, what Mathlib is, lakefile.toml `[[require]]` setup with
   `rev = "v4.31.0"`, `lake exe cache get`, `.lake/` note, ground rules);
   Part-II bullet and Part-VII intro adjusted; every "no libraries/from scratch"
   claim swept (ll.198–212, 232 kept as Part-I-only claims, 3540, 4541).
6. **Ch. 1 order block (ll.519–595)** — replaced by the working development
   (LE/LT instances, order toolbox, fixed `no_overflow`, `strong_ind` via MyNat
   lemmas, `well_ordering` via strong induction + `Classical.em`), split into
   three listings with connecting prose.
7. **Quot.lift2 (ll.756, 1148–56)** — prose now teaches nested `Quot.lift` with
   two respect proofs; Ch. 5 listing replaced accordingly (plus hand-rolled
   `rabs` with `rabs_zero`/`rabs_add`, since core Rat has no |·|).
8. **Ch. 33 engine** — all five compile-blockers fixed in print: helpers
   `varsOf`/`substVar`/`substExpr`/`isInTermsOf` added; `innerFunctions` moved
   before `tryUSub`, redundant `Pow _ u` alternative dropped (with explanation);
   `liatePriority` loses Arctan/Arcsin (noted as exercise) and gains `.Var _`
   at algebraic priority 2; `partialFracStrategy`/`trigReduceStrategy` stubs
   printed; `tryIBP`/`integrate`/`sumStrategy`/`constMulStrategy` now in a
   `mutual` block of `partial def`s with honest prose about the unproven
   termination; naive-`tryUSub` honesty note added.
9. **Capstone outputs** — all printed outputs now byte-match the verified
   program (checked by `#eval` in CalculusVerification.lean): x·sin x trace,
   x²·sin x CLI trace (Power Rule as leaf, threaded result), and
   `∫(x * exp(x)) dx = x * exp(x) - exp(x) + C` (LIATE fix makes IBP succeed;
   prose notes it equals (x−1)eˣ). Honest remark added where `toTrace`'s
   result-threading limitation is introduced; Ch. 34 exercise 4 updated.
10. **Ch. 36 `diff_correct`** — rewritten honestly: real-valued semantics
    `Expr.evalR` (constants via ι : Float → ℝ with ι0/ι1 hypotheses); Const/Var
    cases of `diff` proved against Mathlib's `HasDerivAt` (+ `deriv` remark);
    Add/Sin rule-level lemmas proved; rest an Extended Exercise box; two
    teachable obstacles spelled out (Float is not a normed field & rounding;
    `simplify`'s Float constant-folding is not exact over ℝ). All compiled in
    CalculusMathlibVerification.lean (VCM36).
11. **Smaller failures** — Newton now Float with noncomputability explanation;
    `ftc_part2` restated against Mathlib's interval integral and PROVED
    (one-liner via `intervalIntegral.integral_eq_sub_of_hasDerivAt`), with
    prose owning the switch; `Int.ofFloat`→`Float.toInt64`;
    `String.replicate`→`"".pushn`; `List.bind`→`List.flatMap`; `toTrace` gains
    the SubRule case (with "missing cases" teaching note); `Main.lean` declares
    `Mode` before `Args`; capstone patterns use dot-constructors with an
    explanatory paragraph (typeclass-name ambiguity); Float-literal patterns
    replaced by BEq guards with an explanatory paragraph; `midpoint` positivity
    by `Int.mul_pos` (with pointer to the future `positivity`); `Partition.sorted`
    uses `List.Pairwise (· ≤ ·)`; lakefile modernised (no name/version fields,
    `@[default_target]`) and paths now `.lake/build/bin/...`; `limit_unique`
    rewritten (compiles); `sq_continuous_at` rewritten with
    `mul_lt_mul''`/`div_mul_cancel₀` (compiles); `const_deriv`/`id_deriv`
    rewritten (`div_self hne`); Ch. 4 proofs rewritten with core omega/gcd
    (no `Nat.not_dvd_iff_odd`). NOTE: current Mathlib renames `abs_add` →
    `abs_add_le`; all listings use the new name.
12. **No Lean intro** — new Appendix A "A Lean 4 Primer" (~18 pp.): declarations
    (inductive, def/patterns, theorem/Prop, typeclasses/instances, @[simp]),
    core tactics (rfl, intro, exact/apply, rw, simp/simpa, induction-with **with
    Nat.rec desugaring**, cases, obtain/rcases **with match/Exists.elim
    desugaring**, constructor, calc **with Trans.trans desugaring**,
    have/show/suffices, omega, decide, grind, funext), the Quot API with a
    complete parity miniature, and Mathlib tactics (linarith, nlinarith,
    norm_num, positivity, push_neg, by_contra **with Classical.byContradiction
    desugaring**, ring/ring_nf, set, field_simp, by_cases/unfold). Every example
    compiled (PrimerAppendix in the core file; VCMPrimer in the Mathlib file).
    Forward pointer added at the first listing of Ch. 1 and in the Preface.
13. **Concepts undefined** — limsup defbox added before Cauchy–Hadamard
    (tail-sup definition, MCT existence argument, (−1)ⁿ example); metric-space
    glosses added at both mentions (ll.980, 1766); honest remarkbox added in
    Ch. 10 on where sin/cos/exp come from (power series; Mathlib provides them);
    MyReal→Real switch handled by §6.1 (see item 5).
14. **Decorative claims / cross-references** — propagator-network claim replaced
    (both occurrences) by an honest first-match-short-circuit description;
    "lambda calculus book" reference generalised; Ch. 36 "Connections" section
    reframed to neighbouring *fields* with no companion-book presumptions;
    "ML/AI book" and "optimisation book" references removed.
15. **Minor inconsistencies** — Ch. 2/3 tense fixed; "Chs. 26, 27" → Ch. 26;
    FTC-2 tautological calc replaced by the evaluate-the-constant argument;
    "halves quadratically" → "roughly squared (quadratic convergence)";
    l.353 termination claim corrected (convention, not necessity — either
    argument works, structural descent is what matters).

Additional fixes beyond the review:

- l.1176 falsely claimed Mathlib has a constructive Cauchy-with-modulus branch
  ("Mathlib.Topology.Algebra.Order ... constructive fragment"); rewritten
  (CoRN cited instead; Mathlib described as classical).
- Ch. 23 `partialDeriv` reformulated with Mathlib's `deriv` +
  `Function.update` (compiles); `HasTotalDerivAt` given explicit binders.
- Ch. 21 `expTaylor` marked noncomputable with explicit ℝ-cast of the
  factorial (as printed it also failed elaboration).
- Monofont pinned to the system DejaVu 2.37 TTFs (TinyTeX ships DejaVu 2.34,
  which lacks U+2223 used in the Ch. 4 listings).

Deferred (deliberate):

- The book's own pedagogical sorries remain (Chs. 10, 11, 15, 20–22, 31, and
  the Ch. 36 extended exercise), each now explicitly labelled as an exercise
  in both the listing and the prose.
- Ch. 33's `tryUSub` remains too weak to fire on ∫2x·e^{x²} (now stated
  honestly in prose; strengthening the simplifier is an exercise).

## Toolchain note (2026-07-05, post-resolution)

Repo `lean-toolchain` bumped v4.28.0 → v4.31.0; all files re-verified on v4.31.0.
`CalculusVerification.lean` exit 0 (12 book sorries), `CalculusMathlibVerification.lean`
exit 0 against Mathlib v4.31.0 (8 book sorries; `push_neg` deprecation warnings only —
it is being renamed to `push Not`). `Calculus.lean` needed a whitespace-only fix
(v4.31 requires the tactic block after `:= by` to be indented).
