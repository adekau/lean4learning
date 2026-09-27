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

## Second pass (2026-09-27)

Full re-read of all 5,528 lines (post-edit count). No Lean or LaTeX run (network policy);
Lean listings were checked against `CalculusVerification.lean` /
`CalculusMathlibVerification.lean`. Line numbers refer to the .tex after these edits.

**Verdict.** The July fixes hold up. The book is now in good shape. This pass found
errors of a different kind: several false exercise statements, historical misattributions,
one mathematically false claim in a history box (a "complete ordered field with
infinitesimals"), and a real usability bug in the Mathlib setup instructions (name clashes
with Mathlib's `ContinuousAt`/`HasDerivAt`). No Lean code was changed except comments.

### Fixed — correctness

- **l.1127** Robinson's hyperreals described as a "complete ordered field containing
  genuine infinitesimals". This is impossible, because a complete ordered field is ℝ, which
  is Archimedean. It now reads: an ordered extension of ℝ that is necessarily not complete
  or Archimedean.
- **l.1437** §6.1 told readers to `import Mathlib` and then define `ContinuousAt` and
  `HasDerivAt` at top level. Mathlib already declares both, so Lean would reject the
  definitions (the verification file silently wraps them in `namespace VCM`). A sentence
  now tells readers to put their definitions in a namespace. This also makes the Ch. 16
  `_root_.HasDerivAt` remark coherent.
- **l.3394** (Ch. 25, Ex. 2) claimed f = xy·sin(1/(x²+y²)) has equal mixed partials at
  the origin. In fact f_x(0,k) = k·sin(1/k²), so f_xy(0,0) does not exist. The exercise
  now uses f(x,y) = φ(x)φ(y) with φ(t) = t²sin(1/t), which does have equal but
  discontinuous mixed partials.
- **l.2380** (Ch. 12, Ex. 2) "f′ ≥ 0 and not identically zero ⇒ strictly increasing" is
  false. It now says f′ does not vanish identically on any subinterval.
- **l.2527** (Ch. 14, Ex. 4) "every cubic has a real critical point" is false
  (x³ + x has none). It now asks for exactly one inflection point.
- **l.2802** (Ch. 16, Ex. 4) The hint 1_ℚ is not Riemann integrable, so F is undefined.
  The hint now uses a step function at x = 1/2.
- **l.4176** (Ch. 32, Ex. 3) The claimed result `Add (diff u).1 (diff v).1` ignores the
  `fullSimplify` that `diff` applies. The statement now includes `.fullSimplify`.
- **l.4008** (Ch. 31, Ex. 4) asked for a proof of `e.simplify.eval env = e.eval env`,
  which is false for Float: `Mul (Div 1 0) 0` evaluates to NaN but simplifies to `Const 0`.
  The exercise is reworded as "try to prove", gives the counterexample and points to Ch. 36.
- **l.4837** (Ch. 36 theorem box) said the `Abs` case of `diff` is correct under side
  conditions, but the shipped `Abs` case always returns 0. `Tan` was missing from the
  side-condition list. `Abs` is replaced by `Tan`, and a parenthetical notes that the `Abs`
  placeholder is wrong.
- **l.4937** "Our correctness theorem guarantees that everything we do return is correct".
  No such theorem exists: `integrate` has none, and `diff` has only rule-level lemmas. The
  sentence is now conditional.
- **l.2430** Taylor proof: "Apply the MVT … to obtain Cauchy's MVT form of the remainder".
  It now reads: apply *Cauchy's* MVT to g and h to obtain the *Lagrange* form (re-derived).
- **l.2516** The Newton-iteration comment skipped an iterate (showed 1.4166 → 1.41421356).
  It now shows 17/12 → 577/408 ≈ 1.41421568 → 1.41421356.
- **l.316** The Peano paragraph said the cycle {0,1,2} satisfies P5 and then that P5 rules
  it out. This contradicts itself. P4 (with P3) rules out cycles, and P5 rules out extra
  elements. "Every number has a unique predecessor" is changed to "at most one" (0 has none).
- **l.1359** "Completeness is not a theorem but an axiom … we have constructed ℝ to have
  it." This contradicts itself. It now says completeness is not a consequence of the
  ordered-field axioms: axiomatic treatments postulate it, and here it is a theorem.
- **l.878** "all ring axioms; *in particular* an integral domain" is changed to "moreover".
- **l.357** "Mathlib … flags which results require Classical axioms" was false. It now
  says Mathlib is classical and that `#print axioms` reports dependence on
  `Classical.choice`.
- **l.4189** Non-existence of elementary antiderivatives was credited to "Risch's
  theorem". It is now credited to Liouville's theorem.
- **l.4359** The inverse-trig constructors are Ex. 2 of Ch. **31**, not Ch. 32.
- **l.1745** "sequential characterisation (the next theorem) … bridge theorem below".
  That theorem is the *previous* one, so the wording now says so.
- History:
  - **l.1008** Euclid did not prove the fundamental theorem of arithmetic in Book IX, and
    "p | n² ⇒ p | n" is not Gauss's. This is now Euclid's lemma (Book VII), with FTA
    explicitly first proved by Gauss (1801).
  - **l.1121** In 1858 Dedekind taught at the Zürich Polytechnic, not Göttingen.
  - **l.1125** The infinite-decimal construction is no longer attributed to Weierstrass
    (his construction used aggregates, not decimals).
  - **l.1401** Cauchy's three textbooks span 1821–1829 (*Leçons sur le calcul
    différentiel* is 1829), not 1821–1823.
  - **l.1782** The Hermite quote is corrected to *cette plaie lamentable* (letter to
    Stieltjes, 1893). The book had printed "un fléau déplorable".
  - **l.2035** Leibniz did see some of Newton's manuscripts in London in 1676. The false
    accusation was plagiarism.
  - **l.2548** Barrow is dated "around 1665" here but *Lectiones* 1670 at l.2728. Both now
    say 1670.
  - **l.2965** Dirichlet (1837) proved that absolutely convergent series can be rearranged.
    The any-value rearrangement theorem is Riemann's (1854). The "we prove in this chapter"
    claim is changed, because the chapter only states the theorem.
  - **l.3657** "Earlier versions were known to … Hankel" is impossible (Hankel was born in
    1839). The dubious "Brioschi 1854" claim is replaced by the standard account: the first
    published proof is Hankel (1861).
  - **l.3697** "the Kelvin–Stokes theorem in fluid mechanics" is circular (it *is*
    Stokes' theorem). This is now Kelvin's circulation theorem.

### Fixed — prose

About 12 small edits:
- l.817/829: listing comments said Z is built on MyNat and uses the MyNat cancellation
  law, but the code uses built-in `Nat` and `omega`.
- l.882: prose aligned with the code.
- l.860: "numerators and denominators" for pairs of differences.
- l.906: dependent-types sentence ("type of a value depends on a proof") now reads "type
  of `den_pos` depends on the value of `den`".
- l.1721: "the absolute value |x|/x".
- l.1951: "completeness of the Riemann integral" changed to "Riemann integrability of
  continuous functions".
- l.2037: "replace X for Y" changed to "substitute X for Y".
- l.2785: "whichever is larger" changed to "whichever order".
- l.2167/2281/2287: the three Ch. 10–11 `sorry`s are now labelled "exercise" as the
  Preface promises.
- l.5318: "constants multiples".
- l.5402/5521: the primer's "Mathlib tactics" section said every entry needs Mathlib, but
  `by_cases`/`unfold` are core. It also said they were "seen in Chapter 36", but `unfold`
  is used in Ch. 22.

### Flagged, not changed

- **l.3903–3920, 4716–4749:** The tokeniser and parser are `sorry` ("full implementation
  in the Lake project"), and that project is not printed. The CLI transcripts are still
  presented as "actual output", and Ex. 35.1 asks readers to build and run it. The printed
  code cannot produce them: the `--expr` path goes through `parseStr`. The engine outputs
  themselves match the `#eval` checks. Suggest printing a parser or rewording.
- **l.262:** "Dedekind (1872) defined the integers and rationals via equivalence
  classes". The 1872 work is on cuts. Attributing the pair constructions to Dedekind in
  1872 is doubtful.
- **l.1010, 1077:** "did not arrive until 1872" and "Cantor (1872)" omit Méray (1869),
  who published a Cauchy-sequence construction earlier. This is a common simplification,
  so I left it.
- **l.1403:** ε/δ "appear to have been introduced by Weierstrass". Cauchy already used
  ε and δ (e.g. 1823). The claim is hedged, so I left it.
- **l.1337:** Bishop "located set … strictly weaker conclusion", and "every classically
  valid theorem is also constructively valid if you add enough hypotheses". Both are
  imprecise. The standard fact runs the other way (constructive ⇒ classical).
- **l.3549:** The (x²−y²)/(x²+y²)² Fubini counterexample is attributed to Tonelli.
  I could not confirm this attribution.
- **l.3661:** "Cartan (1899–1945)" reads like a lifespan (he lived 1869–1951). It is
  probably meant as his working period.
- **l.4137:** `diff`'s `Abs` case returns 0 (acknowledged in a comment only). A
  user-visible CLI would print wrong derivatives for |x|.
- **l.4388:** "terminates in practice because each remainder is strictly simpler" is not
  generally true of IBP remainders. It is hedged.
- **l.2469, 3378, 3424:** minor hypothesis looseness in the first-derivative test,
  "twice continuously differentiable *at* a", and "semidefinite ⇒ inconclusive" (should
  be singular/semidefinite-but-not-definite). This is textbook-standard informality.
