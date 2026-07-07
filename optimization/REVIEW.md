# Proofreading review: verified-optimization.tex

Reviewed 2026-07-06 (full 3,199-line sequential read). All Lean code was extracted
and compiled against toolchain **leanprover/lean4:v4.31.0**. Two companion files:

- `OptimizationVerification.lean` — **core Lean only** (no packages), compiles clean.
- `OptimizationMathlibVerification.lean` — the listings that need `Finset`,
  `SemilatticeSup`/`⊔`, or `BinaryHeap`; verified in a **Mathlib v4.31.0** scratch
  Lake project. Compiles clean.

Every applied fix is marked `-- DEVIATION` (with the exact compiler error) or
`-- DEVIATION (stub)` (helper the book references but never defines); every
`sorry` is marked `BOOK'S OWN SORRY` where the book prints one, otherwise it is a
deviation noting the book's proof is pseudo-code. Line numbers refer to the .tex.

## Verdict

The combinatorial-optimization *narrative* is pedagogically pleasant and mostly
sound at the survey level (branch-and-bound structure, Lagrangian relaxation
direction, Pareto partial-order, simulated-annealing constants). But the book's
central promise — a **verified** solver with a machine-checked soundness theorem —
is not delivered, and there is a **fundamental modelling error** that makes the
headline theorem false as stated:

1. **Soft objective vs. hard propagation.** The objective is a *soft* asymmetric
   penalty (missing a stat target is penalised, not forbidden), yet the `LinearGeq`
   propagator and `solve` treat stat targets as *hard floors* and delete any combo
   that cannot reach them. So propagation can prune the true penalty-minimiser, and
   `solve` can return `.infeasible` for a problem that has a perfectly good
   minimum-penalty answer. `propagation_preserves_optimal` (tex 2434) and the
   `.infeasible` arm of `solver_sound` (tex 2385) are therefore **false**.

2. **Nothing is actually proven.** *Every* non-trivial theorem in the book is
   `sorry` (`canonical_exists`, `dominates_trans` as printed, `linearGeq_sound`,
   `propagation_preserves_optimal`, `lp_bound_valid`, `bb_step_preserves`,
   `infusion_dp_optimal`, and the capstone `solver_sound_proof`, whose printed proof
   body is pseudo-Lean that does not elaborate). A software-engineer reader will
   reasonably believe the solver is verified; it is not.

3. **Undeclared Mathlib dependency.** As with the sibling calculus book, the text
   silently mixes core-Lean code with code that only compiles against Mathlib
   (`Finset`, `SemilatticeSup`, `BinaryHeap`). The book never states a toolchain or
   a library requirement. This should be flagged as prominently as calculus/ now
   flags its own split.

4. **Almost no printed listing compiles verbatim.** Removed/renamed v4.31 API
   (`List.bind`, `List.enum`, `Array.mkArray`, `Float.max`, `Float.toNat`,
   `BitVec.popcount`), `Nat.max` used as a sentinel *value*, `Finset.fold` misused
   as an accumulator, `Finset.isEmpty`/`Finset.toList` issues, and roughly two dozen
   helper functions that are used but never defined.

The two worked numeric examples I could recompute (the Ch. 6 propagation trace and
the Ch. 4 LP-duality statement) are **both wrong**.

## Math errors

1. **tex 1073–1084 — LP weak duality: inequality flipped / wrong dual pairing.**
   Theorem box states, for primal `min cᵀx s.t. Ax ≤ b, x ≥ 0` and dual
   `max bᵀy s.t. Aᵀy ≥ c, y ≥ 0`, that `cᵀx ≥ bᵀy`. The book's own proof derives the
   **opposite**: `cᵀx ≤ (Aᵀy)ᵀx = yᵀAx ≤ yᵀb = bᵀy`, i.e. `cᵀx ≤ bᵀy`. With these
   constraint directions the "dual" is an *upper* bound on the primal min, not a
   lower bound, so it cannot serve as the optimality certificate the book claims
   (tex 1091–1101). The standard lower-bounding dual of a `min cᵀx s.t. Ax ≥ b`
   primal is `max bᵀy s.t. Aᵀy ≤ c` — the book has the `Ax ≤ b` / `Aᵀy ≥ c`
   directions backwards. Counterexample to the *stated* `≥` (verified in Lean,
   core file): `A=(1), b=(1), c=(1)`; primal `x=0` feasible, `cᵀx=0`; dual `y=2`
   feasible, `bᵀy=2`; `0 ≥ 2` is false.

2. **tex 1383–1413 — Ch. 6 worked example: wrong propagation outcome.** Target
   Power ≥ 300, three slots, "no infusions in this simplified version". Maximum
   achievable Power is 141+94+47 = **282 < 300**, so under the no-infusion rule the
   `LinearGeq` propagator empties *every* domain (the instance is infeasible) — it
   does **not** leave `{Berserker's, Marauder}` on every slot as claimed at tex 1393.
   Even with the propagator's usual +90 infusion budget (as defined tex 794–820),
   only *coat*-Celestial is removed (67+94+47+90 = 298 < 300); Celestial survives on
   leggings (322 ≥ 300) and boots (347 ≥ 300). Machine-checked in the core file
   (`ch6Survivors`): budget 0 ⇒ `[[],[],[]]`; budget 90 ⇒ coat loses only Celestial.
   The chapter then admits at tex 1404 that all-Berserker's reaches only 282 — which
   directly contradicts its own Step-1 claim that the target constrained the domains
   to `{Berserker's, Marauder}`.

3. **tex 794–820, 2397–2446, 2376–2387 — soft/hard mismatch makes soundness false.**
   See Verdict #1. The prose "proof" at tex 2402–2415 even argues that a combo pruned
   for being unable to *reach* a target is "suboptimal" — false for a soft penalty:
   the pruned combo may give the *smallest* shortfall and hence the *lowest* penalty.

4. **tex 2428 — `linearGeq_sound` conclusion is over-strong (false as stated).**
   It concludes `statTotal b s + 90 < targets s`. But `statTotal` (tex 468) already
   includes up to `5·18 = 90` infusion points, so from the removal condition one can
   only derive `statTotal b s < targets s`. Putting all 18 infusions on `s` gives a
   counterexample to the printed `+ 90` version.

5. **tex 1623 — subgradient step size is constant, not "diminishing".**
   `stepSize := 1.0 / (1.0 + iters.toFloat)` uses the *total* iteration count
   (`iters`, a fixed argument), so every iteration uses the same step. The comment
   and prose (tex 1595–1599) call for a diminishing schedule; it should depend on the
   current iteration index `k`.

6. **tex 513 — search-space size off by ~3.5×.** `40^16 ≈ 4.29×10^25`, not the
   stated `1.2×10^25` (verified). Minor. (`15^16 ≈ 6.57×10^18` at tex 594 is fine.)

## Lean errors

All reproduced with the compiler; fixes in the two verification files. "(core)" =
verified in `OptimizationVerification.lean`, "(mathlib)" = verified in
`OptimizationMathlibVerification.lean`.

1. **tex 460–472 (core) — `Build`/`statTotal` reference undefined `Rune` and
   `GearSlot.all`.** `Rune` is promised "to be defined later" and never is;
   `GearSlot.all`, `StatType.all`, `allCombos`, and the scalars `wMiss`/`wOver`
   (used from tex 1348 onward) are likewise never defined. Stubbed so the ~30
   downstream listings elaborate. A reader cannot run *any* program as printed.

2. **tex 1604–1628 (core) — subgradient/`lagrangianDual`: five compile errors.**
   `armourSlots.pairs` (no `List.pairs`); `lambda.zipWith violations.toArray f`
   (in v4.31 `Array.zipWith` takes the function *first* — "Application type
   mismatch"); `Float.max` ("Unknown constant `Float.max`", use `max`);
   `Array.mkArray` (removed in v4.31 → `Array.replicate`); and the final
   `|>.map fun (bound,_,sol) => …` on a 3-tuple where the result type is a pair
   (`Prod.map` needs two functions). `none` also needs a type ascription.

3. **tex 1749–1768 (core) — `allNeighbours`/`allMoves`: `GearSlot.all.bind`.**
   `List.bind` was removed in v4.31 ("Unknown constant `List.bind`", now
   `List.flatMap`).

4. **tex 1793–1802 (core) — `hillClimbRestarts`: three errors.** `Nat.max` used as a
   sentinel *value* — it is the binary max **function** ("Application type mismatch:
   Nat.max has type Nat → Nat → Nat but is expected to have type Nat"); the binder
   named `local` is a reserved keyword ("unexpected token 'local'"); and the trailing
   `|>.fst` returns only `Build` from a `Build × Nat × StdGen` while the signature
   promises `Build × Nat`.

5. **tex 1844–1861 (core) — `saStep`: `(neighPen - currentPen : Float)`.** Core Lean
   has no `Nat → Float` coercion ("Type mismatch: a - b has type Nat but is expected
   to have type Float"). Fixed with `.toFloat`. (Also `randomSlot`, `randomCombo`,
   `randomFloat`, `availableCombos` undefined.)

6. **tex 1903–1931 (core) — `tabuStep`: `Nat.max` sentinel again**, plus
   `allNeighbourMoves`, `defaultCombo`, `setBuildSlot` undefined. The comment
   "OR if it produces a new global best" (aspiration criterion) is *not* implemented.

7. **tex 2069–2093 (core) — `dominates_trans` and `paretoFrontier`.** The printed
   proof writes `Nat.le_trans (hbc.1 s) (hab.1 s) |>.symm` and
   `Nat.lt_of_lt_of_le hs (hbc.1 s) |>.symm` — `≤`/`<` have no `.symm`
   ("Invalid field `symm`: … `Nat.le.symm`"), and a `sorry` follows each `exact`
   ("No goals to be solved"). The second branch also composes in the wrong direction
   (needs `Nat.lt_of_le_of_lt (hbc.1 s) hs`). Separately, `paretoFrontier` (tex 2082)
   uses `dominates` (a `Prop`) inside `List.any` **before** the `Decidable` instance
   (tex 2087) is declared — "failed to synthesize Decidable"; the instance must
   precede it.

8. **tex 2225–2243 (core) — `infusionDP`: the most broken listing (7 issues).**
   `Array.mkArray` (removed); `stats.foldl … fun dp i stat =>` (foldl's step takes
   *two* args, three given); the fold body returns one row but the accumulator is the
   whole table; `.mapIdx fun r _ => … r.val` (v4.31 `Array.mapIdx` passes a `Nat`, so
   `r.val` fails — "Unknown field `val`"); `(Nat.max, #[])` sentinel;
   `stats.indexOf` (→ `Array.idxOf`); and a semantic bug — `allocRest.push ni`
   appends at the *end* while extraction reads position `i`, reversing the allocation.
   A minimally-repaired, **runnable** version is in the core file; its `#eval` on a
   toy instance returns the correct optimal allocation `[8,10,0,…]` with penalty `0`.

9. **tex 2654–2661 (core) — BitVec domain.** `d.popcount` — no `BitVec.popcount` in
   v4.31 (it is `BitVec.cpop`, returning a `BitVec`, so `.toNat` is also needed); and
   `d &&& ~~~(1 <<< i.val)` fails because `1 <<< i.val` elaborates at `Nat` and `~~~`
   then needs `Complement Nat` ("failed to synthesize"). The literal must be ascribed
   `(1 : BitVec 40)`. Repaired `#eval` returns `39`.

10. **tex 2717–2740 (core) — incremental propagation.** `state.dirty.toList.enum` —
    `List.enum` removed in v4.31 (now `List.zipIdx`, which additionally yields
    `(elem, idx)` not `(idx, elem)`, so the projections must swap). Plus
    `linearGeqFilter`, `GearSlot.toIdx` undefined.

11. **tex 2779–2793 (core) — compiler hints.** `contribution'` reads `contribTable`
    but the earlier listing defines `buildContribTable` (name drift);
    `@[specialize] def propagateWith [BEq D] [Domain D]` — `Domain` is an `abbrev`
    for `BitVec 40`, not a class ("invalid binder annotation, type is not a class");
    `Propagator` type undefined.

12. **tex 3002–3024 (core) — `paretoFrontierMode`.** `(w * 100).toNat` — no
    `Float.toNat` in v4.31 ("Unknown constant"). Also `{ problem with
    wMissPerStat := … }` uses a `GearProblem` field that appears *nowhere else*;
    every other listing uses the global scalars `wMiss`/`wOver` (notation drift).

13. **tex 570–586 (mathlib) — `Cell`/`runToFixpoint`.** `SemilatticeSup` and `⊔` are
    Mathlib order classes (not core Lean); `PropNetwork` undefined.

14. **tex 806–929 (mathlib) — the three propagators.** Use `Finset` (Mathlib).
    `maxContribForStat`/`minContribForStat` undefined. `minContribForStat` over an
    *empty* Finset has no natural neutral element — a gap the monotonicity proof at
    tex 884–891 silently ignores (min over a smaller set is ≥ only for **nonempty**
    sets, and domains here can go empty).

15. **tex 1263–1281 (mathlib) — `orderCombos` is noncomputable.** It calls
    `Finset.toList`, which in Mathlib is `noncomputable` ("failed to compile
    definition … depends on 'Finset.toList'"). So even granting Mathlib, the book's
    value-ordering (and, transitively, any `.toList` over a `Finset` domain in
    `backtrack`/`branchAndBound`) **cannot execute**; a real solver needs
    `Finset.sort` or a list-backed domain.

16. **tex 1334–1359 (mathlib) — `backtrack`.** `(domains' s).isEmpty` — Mathlib
    `Finset` has no `isEmpty` field ("Invalid field `isEmpty`"); and
    `(domains' slot).fold best fun acc combo => …` misuses `Finset.fold`, which is a
    fold over a **commutative/associative** operation, not a general accumulator loop
    (type error). Same `.fold` misuse recurs in `branchAndBound` (tex 2355).

17. **tex 1449–1472 (mathlib) — A* skeleton.** `SearchNode … deriving Repr` fails —
    the `domains` field is a *function*, so `Repr` cannot be derived. `BinaryHeap` is
    `Batteries.BinaryHeap` (needs `open Batteries`). `queue.extractMin` does not
    exist — only `extractMax`, which returns `Option α × BinaryHeap …`, **not**
    `Option (α × …)`, so the `| some (node, queue')` match is ill-typed. Also: with
    the comparator `·.fCost < ·.fCost`, `extractMax` pops the **largest** f-cost — a
    max-heap — but best-first search needs the *smallest* f. `expandNode` undefined.

18. **tex 2313–2360 (mathlib) — the complete solver (`solve`).**
    `simulatedAnnealing domains problem.targets` is missing the `rng` argument (only
    `maxIters` is defaulted); the result is a `Build × Nat` pair, but the next line
    passes it to `totalPenalty` as a `Build`. `anyDomainEmpty`, `allSingleton`,
    `gearStats`, `solveLPRelaxation`, `smallestDomainSlot`, `infusionDP` are all
    out of scope. `branchAndBound`'s `else` branch produces `Build × Nat` where the
    signature demands `Option (Build × Nat)` (missing `some`). And
    `branchAndBound` **never returns `none`**, so `solve`'s `| none => .infeasible`
    is dead code — the printed solver cannot report infeasibility from B&B at all.

19. **tex 2602–2630 (mathlib) — `solver_sound_proof` is pseudo-Lean.** `unfold solve`
    produces one goal, but the proof immediately uses case bullets `·` ("no goals" /
    unexpected bullet); "case 1" does `intro b hfeas` on a `match` goal without
    `split`; and `propagation_preserves_optimal ..`, `domain_empty ..`,
    `extractBuild_feasible ..`, `bb_invariant_at_termination ..`, `queue_empty ..`
    are undefined identifiers. Replaced wholesale by `sorry`.

20. **tex 2520–2535 (mathlib) — `BBInvariant`.** `totalPenalty b ≥ …` compares a
    *partially applied* 4-argument function to a `Nat` (type error — the
    targets/weights are missing). `BBState`/`BBNode` undefined.

## Learning gaps

1. **"Verified" is aspirational, not real.** The book's structure and title promise a
   verified solver; in fact every proof is `sorry` and the capstone proof does not
   even parse. For the target reader (SWE, minimal proof-assistant experience) this
   is the most important thing to state up front. The book should either mark these
   as "specification only / proofs left as exercises" throughout, or actually
   discharge at least the small ones (`dominates_irrefl`/`dominates_trans` are
   genuinely provable and would make a good first win — see the core file, where the
   book's own trailing sorries are removed and the goals close).

2. **No Lean tactic primer.** The book uses `intro`, `exact`, `constructor`,
   `obtain`, `unfold`, `rfl`, and `sorry` with zero introduction, and no appendix
   explains them. The reader's other books (per the repo memory) gained "tactic
   primer" appendices with desugarings; this book needs the same, especially since
   the proofs shown are the *broken* ones.

3. **Undeclared Mathlib dependency (see Verdict #3).** The reader is told the
   prerequisites are "Lean 4 typeclasses, basic tactic proofs, and the lattice book"
   (tex 232) with no mention that `Finset`, `SemilatticeSup`, and `BinaryHeap`
   require Mathlib + Batteries. A one-paragraph "which parts need Mathlib" box (like
   calculus/ now has) would fix this.

4. **Matrix/transpose notation unexplained.** LP duality (tex 991, 1073, 1081) uses
   `cᵀx`, `Aᵀy`, `yᵀAx` with no reminder of what transpose/inner-product means — the
   one place the book leans on linear-algebra notation for a reader who may not have
   it.

5. **Title/preface over-promise continuous optimization.** "Convex optimization,
   gradient descent, Newton's method" are named (tex 678–694) but Newton's method is
   never developed and convexity gets a single page before the book (correctly)
   pivots to combinatorial methods. Reset expectations in the preface: this is a
   discrete/combinatorial optimization book.

6. **Nothing runs.** Because ~two dozen helpers (`GearSlot.all`, `allCombos`,
   `wMiss`, `Rune`, `propagateToFixpoint`, `solveLPRelaxation`, …) are referenced but
   never defined, and `Finset.toList` is noncomputable, the reader cannot execute a
   single end-to-end example. The exercises repeatedly say "run it / measure it" with
   no runnable substrate.

## Internal inconsistencies (minor)

1. **Slot count drift.** `GearSlot` has **14** constructors, but tex 513 says
   "approximately 16 gear slots", the `PropState` comment (tex 2718) says
   "16 entries", and `UndoEntry`/`saveState` use `Fin 16` (tex 2756–2761). The
   `subgradientStep` comment "C(6,2) = 15 pairs" (tex 1618) is correct for the 6
   armour slots.
2. **`contribTable` vs `buildContribTable`** (tex 2693 vs 2781) — name mismatch.
3. **Two incompatible LP interfaces.** `solveLPRelaxation` returns a bare bound
   (`Nat`/`Float`, tex 2350) in `branchAndBound`, but `lp_bound_valid` (tex 2477)
   treats it as a record with `.objectiveValue`. Never reconciled.
4. **`wMissPerStat` field** (tex 3009) exists on `GearProblem` nowhere else; the rest
   of the book uses global `wMiss`/`wOver`.
5. **`traitStatTotal` accumulator bug (tex 2905–2913).** The `foldl`'s `then` branch
   returns `conv.percentage * …` and *discards* `acc`, so with several conversions
   into the same stat only the **last** counts. Should be `acc + conv.percentage*…`.
   Machine-demoed in the core file: two 10% conversions into Power yield `4.0`, not
   the correct `9.0`.
6. **`extractNogood` keeps the wrong assignments (tex 1517–1524).** For a stat-*floor*
   (LinearGeq) failure the culprits are the slots contributing *too little*; the code
   keeps those with `contribution … > 0`, which is not a provably-inconsistent set,
   so the "nogood" is unsound.
7. **`selectSlotFailFirst` panics on all-singleton input (tex 1249–1254).** `unfixed`
   is then empty and `unfixed.head!` traps at runtime; never guarded.
8. **No toolchain claim anywhere.** Unlike the calculus book (which falsely claimed
   "no Mathlib"), this book states no version at all — so there is no false version
   claim to correct, but also no signpost that the code targets any particular Lean.

## Verification summary

- **`OptimizationVerification.lean`** (core Lean, v4.31.0, no packages): compiles
  clean. `sorry` count = 6 declaration-warnings, all accounted: `canonical_exists`,
  the `Decidable (dominates)` instance (4 internal sorries, book's own, one
  warning), `solver_sound`, `bb_step_preserves`, `infusion_dp_optimal`,
  `propagateWith` — every one is a BOOK'S OWN SORRY or a book statement printed
  without proof. Runnable `#eval`s
  confirm: repaired `infusionDP` toy optimum `[8,10,0,…]`/penalty 0; `BitVec` domain
  card 39; `traitStatTotal` bug (4.0 vs 9.0); Ch. 6 propagation survivors
  (`[[],[],[]]` at budget 0; coat-only-Celestial-removed at budget 90); and the LP
  weak-duality counterexample.
- **`OptimizationMathlibVerification.lean`** (Mathlib v4.31.0 scratch project at
  `…/scratchpad/mathlib-verify-431`): compiles clean. `sorry` count = 4, all
  BOOK'S OWN SORRY (`linearGeq_sound`, `propagation_preserves_optimal`,
  `lp_bound_valid`, `solver_sound_proof`).
- Neither file has any error; all `sorry`s are deliberate (book's).

## Coverage

Read all 3,199 lines and 15 chapters + 2 appendices. **Every** Lean listing
(38 `leanbox`/`minted` blocks plus the two in-theorem listings) was extracted,
compiled, and recorded — 14 in the core file, the `Finset`/`SemilatticeSup`/
`BinaryHeap` ones in the Mathlib file, with cross-references where a listing depends
on definitions from another chapter. All prose claims about Lean were checked. Math:
recomputed the Ch. 6 propagation trace, the Ch. 4 LP-duality statement, the SA
temperature/cooling constants, the tabu tenure, the infusion-DP complexity, and the
search-space sizes; re-derived the convexity, weak-duality, weak-Lagrangian-duality,
Pareto partial-order, and A*-admissibility arguments. Not independently re-derived:
the illustrative benchmark node counts (tex 2807–2812), which the book itself labels
"illustrative".

## Resolution (2026-07-06)

Patched in place. Toolchain pinned to **leanprover/lean4:v4.31.0**. Both
verification files recompile clean (`lake env lean`): core = 6 `sorry`
warnings, Mathlib scratch = 4 `sorry` warnings — every one an intentional
BOOK'S OWN SORRY / honest specification (details below). PDF rebuilt with
`latexmk -xelatex -shell-escape` to **81 pages**, no undefined refs, no missing
glyphs (system DejaVu pinned by path; `outputdir=build` dropped for minted v3;
`multirow` installed).

### Modelling reconciliation (Verdict #1, Math #3)
`Build.feasible` now includes the **hard stat floors**
(`∀ s, statTotal b s ≥ targets s`) alongside domain membership and the
18-infusion budget. The solver is thereby reframed as deciding the *hard-floor*
problem: "among builds meeting every target, minimise (overshoot) penalty; else
`.infeasible`." Under this reading `LinearGeq` pruning is sound (a necessary
condition for floor-feasibility), the `.infeasible` arm is true, and `solve`'s
infeasibility branch is made **live** (incumbent is now `Option`, leaves are
accepted only after a `meetsFloors` check, so B&B genuinely returns `none`). A
prominent Warning box in Ch.1 (and again at `LinearGeq` and at the theorem)
states honestly that this is *not* the soft-penalty problem and that `LinearGeq`
can prune the soft optimum. `solver_sound` is stated precisely against this
feasibility and left as an **honest specification** (`sorry`); it is no longer
false.

### Genuinely PROVED (no sorry)
- `dominates_irrefl`, `dominates_trans` (book's `.symm`/wrong-direction bug
  fixed) — core file, both in book and verification.
- `StatType.mem_all` and the `Decidable (dominates a b)` instance — the book's
  four sorries replaced by a boolean test `dominatesBool` + `decidable_of_iff`;
  dominance now computes (`#eval` demonstrated).
- Runnable/executable checks (not theorems, but real machine output): repaired
  `infusionDP` `#eval` → `[8,10,0,…]`, penalty 0; `Domain.card` `#eval` → 39;
  Ch.6 `ch6Survivors`; `traitStatTotal` bug demo (4.0 vs 9.0); LP weak-duality
  counterexample AND the corrected-direction `example`; all Appendix-C primer
  examples (new `Primer` namespace).

### Relabelled as honest SPECIFICATIONS (precise statement, `sorry`, marked)
`canonical_exists`, `linearGeq_sound` (corrected: `+90` double-count removed,
hypotheses added, conclusion is a floor-miss), `propagation_preserves_feasible`
(TRUE replacement for the false `propagation_preserves_optimal`),
`lp_bound_valid`, `bb_step_preserves`, `infusion_dp_optimal`,
`solver_sound`/`solver_sound_proof` (pseudo-Lean body removed). `propagateWith`
remains a stub `def` body `sorry`.

### Math errors
1. **LP weak duality** — standard form switched to `Ax ≥ b`, dual to
   `max bᵀy s.t. Aᵀy ≤ c, y ≥ 0`; theorem now `cᵀx ≥ bᵀy`, matching its own
   (rewritten) proof and the lower-bound certificate claim. Added a
   transpose/inner-product notation box. Corrected direction machine-checked.
2. **Ch.6 worked example** — rewritten to the machine-checked outcome: at
   +0 infusions the whole instance is infeasible (max Power 282 < 300); with the
   propagator's +90 budget only *coat*-Celestial is removed (leggings/boots keep
   all three). Steps 1–3 redone.
3. **Soft/hard** — see reconciliation above.
4. **`linearGeq_sound` `+90`** — corrected statement (see specifications).
5. **Subgradient step size** — now `1/(1+k)` on the *current* index `k`
   (genuinely diminishing); fixed in book and core verification file, plus the
   five compile errors (`List.pairs`, `zipWith` arg order, `Float.max`→`max`,
   `Array.mkArray`→`replicate`, tuple `match`).
6. **Search space** — reconciled to the type's **14** slots throughout
   (`40^{14}≈6.9e22`, `15^{14}`, `40×14=560`, neighbourhood `14×39`, benchmark
   `40^{14}`, what-if `40^8`), which also resolves the 14-vs-16 drift. (Chose 14
   over "keep 16 + fix coefficient to 4.29e25", since 16 perpetuated the drift
   with the 14-constructor `GearSlot`.)

### Lean compile errors — all listings corrected to v4.31 API
`List.bind`→`flatMap`; `List.enum`→`zipIdx` (with swapped projections);
`Array.mkArray`→`replicate`; `Float.max`→`max`; `Float.toNat`→`.toUInt64.toNat`;
`Array.indexOf`→`idxOf`; `BitVec.popcount`→`cpop.toNat`; `~~~(1<<<i)` ascribed
`(1:BitVec 40)`; `Nat.max`-as-value → large literal; `Finset.isEmpty`→`card=0`;
`Finset.fold` misuse → `enumerate …|>.foldl`; `Finset.toList` (noncomputable) →
list-backed `orderCombos`/`enumerate` with an explicit Warning box; A* fixes
(no `deriving Repr`, `open Batteries`, `extractMax` pair, comparator reversed to
`>` for min-first); `deriving Repr` on function field removed; `local` keyword
renamed; 3-/6-tuple `|>.map` (`Prod.map`) → `match`; `[Domain D]` → real class
`DomainLike`; `contribTable` defined from `buildContribTable`; the ~two dozen
missing helpers (`GearSlot.all`, `StatType.all`, `Rune`, `allCombos`, `wMiss`,
`wOver`, `comboOrd`, `GearProblem`, …) now defined once in the book.
`solve`/`branchAndBound` rewritten (see reconciliation); dead `.infeasible`
branch made live. Every listing carries a `(Mathlib)`/`(Batteries)` tag when it
needs one.

### Mathlib decision (Verdict #3, Learning gap #3)
New §"Which Parts Need Mathlib" (Ch.1) with the core-vs-Mathlib split, a
lakefile.toml snippet, `lake exe cache get` / `.lake` note, and per-listing tags.
Split reported in verification files' headers.

### Learning gaps
Preface rewritten: honest "verified" Warning box; discrete/combinatorial framing
(Newton's method explicitly set aside); toolchain + Mathlib statement; forward
pointer to the primer. New **Appendix C: A Lean 4 Primer** covering
`inductive`/`def`/`structure`/`instance`/`theorem`, `intro`/`exact`/
`constructor`/`obtain`/`unfold`/`rfl`/`simp`/`omega`/`split`/`induction`/`cases`
(with recursor & `Exists.elim` desugarings) and a blunt account of `sorry` =
"unproven"; every example machine-checked in the core file's `Primer` namespace.
Transpose/inner-product box added to LP duality. The infusion DP is the runnable
end-to-end showcase (`#eval` in the book and verified in the core file).

### Internal inconsistencies
14-vs-16 → 14 everywhere (incl. `Fin 16`→`Fin 14`, "16 entries"→"14",
`PackedBuild` comment). `contribTable`/`buildContribTable` reconciled. Two LP
interfaces: kept both but named them (`solveLPRelaxation : … → Nat` for the B&B
prune, `solveLPRelaxationF : … → LPResult` for reduced-cost/certificates) and
said so. `wMissPerStat` promoted to a real (defaulted) `GearProblem` field.
`traitStatTotal` accumulator fixed (`acc + …`). `extractNogood` now returns the
whole failing assignment (sound) with a Warning that culprit-minimisation is
subtle for floor failures. `selectSlotFailFirst` `head!` panic replaced by a
`match` (total). Toolchain claim added (v4.31.0).

### Deferred (left as honest exercises, clearly marked)
The full proofs of `solver_sound`, `linearGeq_sound`,
`propagation_preserves_feasible`, `lp_bound_valid`, `bb_step_preserves`,
`infusion_dp_optimal`, `canonical_exists`; wiring `wMissPerStat` through
`solve`/`totalPenalty`; sound nogood minimisation; the A*/simplex helper bodies.
The illustrative benchmark node counts are unchanged (labelled illustrative).
