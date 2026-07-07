/- ============================================================
   Verified Optimization — Mathlib companion verification file

   This file verifies every Lean 4 listing in
   optimization/verified-optimization.tex that CANNOT compile in
   core Lean because it uses Mathlib/Batteries-only identifiers:
   `Finset` (every propagator and the whole solver loop),
   `SemilatticeSup` + `⊔` (the Cell type from the lattice book),
   and `BinaryHeap` (A* search).

   *** The book NEVER declares this dependency. *** It presents
   all of this code alongside core-Lean code with no indication
   that `Finset`/`SemilatticeSup`/`BinaryHeap` require external
   libraries. (Same failure mode as the calculus book before its
   "From MyReal to Mathlib" passage was added.)

   REQUIREMENTS: Mathlib (leanprover-community/mathlib4, rev
   v4.31.0) on toolchain leanprover/lean4:v4.31.0. Verified by
   copying this file into a Lake project requiring mathlib
   v4.31.0 and running `lake env lean` there.

   Conventions (as in OptimizationVerification.lean):
     -- DEVIATION (stub): helper the book never defines.
     -- DEVIATION: printed code fails; exact error recorded,
        minimal fix applied.
     -- BOOK'S OWN SORRY: a sorry the book prints deliberately.
   Line numbers refer to verified-optimization.tex.
   ============================================================ -/

import Mathlib

set_option linter.unusedVariables false

namespace VOM

/- ============================================================
   Prelude: the book's core data model (verified verbatim in
   OptimizationVerification.lean; reproduced here so the Finset
   listings elaborate).
   ============================================================ -/

inductive StatType where
  | power | precision | ferocity | toughness | vitality
  | conditionDamage | expertise | concentration | healingPower
  deriving DecidableEq, Repr, Hashable

inductive GearSlot where
  | headgear | shoulders | coat | gloves | leggings | boots
  | mainhand | offhand
  | amulet | ring1 | ring2 | accessory1 | accessory2 | backPiece
  deriving DecidableEq, Repr

inductive ComboCategory where
  | triple | quad | celestial
  deriving DecidableEq, Repr

structure StatCombo where
  name     : String
  category : ComboCategory
  majors   : List StatType
  minors   : List StatType
  deriving DecidableEq, Repr

structure SlotCoefficients where
  tripleMajor  : Nat
  tripleMinor  : Nat
  quadMajor    : Nat
  quadMinor    : Nat
  celestial    : Nat
  deriving Repr

def coefficients : GearSlot → SlotCoefficients
  | .headgear   => ⟨63,  45,  54,  30, 30⟩
  | .shoulders  => ⟨47,  34,  40,  22, 22⟩
  | .coat       => ⟨141, 101, 121, 67, 67⟩
  | .gloves     => ⟨47,  34,  40,  22, 22⟩
  | .leggings   => ⟨94,  67,  81,  44, 44⟩
  | .boots      => ⟨47,  34,  40,  22, 22⟩
  | .mainhand   => ⟨125, 90,  108, 59, 59⟩
  | .offhand    => ⟨125, 90,  108, 59, 59⟩
  | .amulet     => ⟨157, 108, 133, 71, 72⟩
  | .ring1      => ⟨126, 85,  106, 56, 57⟩
  | .ring2      => ⟨126, 85,  106, 56, 57⟩
  | .accessory1 => ⟨110, 74,  92,  49, 50⟩
  | .accessory2 => ⟨110, 74,  92,  49, 50⟩
  | .backPiece  => ⟨63,  40,  52,  27, 28⟩

def contribution (slot : GearSlot) (combo : StatCombo)
    (stat : StatType) : Nat :=
  let c := coefficients slot
  match combo.category with
  | .triple =>
    if combo.majors.contains stat then c.tripleMajor
    else if combo.minors.contains stat then c.tripleMinor
    else 0
  | .quad =>
    if combo.majors.contains stat then c.quadMajor
    else if combo.minors.contains stat then c.quadMinor
    else 0
  | .celestial =>
    let wvwStats : List StatType :=
      [.power, .precision, .ferocity, .toughness,
       .vitality, .conditionDamage, .healingPower]
    if wvwStats.contains stat then c.celestial else 0

structure Rune where  -- DEVIATION (stub): never defined in the book
  name : String
  deriving DecidableEq, Repr

def GearSlot.all : List GearSlot :=  -- DEVIATION (stub): never defined
  [.headgear, .shoulders, .coat, .gloves, .leggings, .boots,
   .mainhand, .offhand,
   .amulet, .ring1, .ring2, .accessory1, .accessory2, .backPiece]

def StatType.all : List StatType :=  -- DEVIATION (stub): never defined
  [.power, .precision, .ferocity, .toughness, .vitality,
   .conditionDamage, .expertise, .concentration, .healingPower]

structure Build where
  gear      : GearSlot → StatCombo
  rune      : Rune
  infusions : StatType → Nat

def statTotal (b : Build) (s : StatType) : Nat :=
  let gearTotal := (GearSlot.all.map fun slot =>
    contribution slot (b.gear slot) s).sum
  gearTotal + 5 * b.infusions s

def penalty (target actual : Nat) (wMiss wOver : Nat) : Nat :=
  if actual < target then wMiss * (target - actual)
  else wOver * (actual - target)

def totalPenalty (b : Build) (targets : StatType → Nat)
    (wMiss wOver : Nat) : Nat :=
  (StatType.all.map fun s =>
    penalty (targets s) (statTotal b s) wMiss wOver).sum

def wMiss : Nat := 10   -- DEVIATION (stub): free globals, never fixed
def wOver : Nat := 1

instance : Inhabited StatCombo := ⟨⟨"", .triple, [], []⟩⟩
instance : Inhabited GearSlot := ⟨.headgear⟩
instance : Inhabited Build := ⟨⟨fun _ => default, ⟨""⟩, fun _ => 0⟩⟩

/- ============================================================
   §Ch.3 — Cell and fixpoint loop (tex 570–586).
   `SemilatticeSup` and `⊔` are MATHLIB order classes — not core
   Lean. `PropNetwork` (with `.fireAll` and `==`) is never
   defined. With a stub, the listing compiles here.
   ============================================================ -/

-- Reusing infrastructure from Verified Order Theory
structure Cell (L : Type) [SemilatticeSup L] where
  value : L

def Cell.update [SemilatticeSup L] (c : Cell L) (new : L) : Cell L :=
  ⟨c.value ⊔ new⟩

-- Domain cell: Finset StatCombo with reverse-inclusion order
-- ⊔ is ∩ (intersection), ⊥ is allCombos, ⊤ is ∅

-- DEVIATION (stub): `PropNetwork` never defined in the book.
structure PropNetwork where
  domains : List (Finset StatCombo)
  deriving BEq
def PropNetwork.fireAll (n : PropNetwork) : PropNetwork := n

-- The propagator loop from the lattice book:
partial def runToFixpoint (network : PropNetwork) : PropNetwork :=
  let network' := network.fireAll
  if network' == network then network'
  else runToFixpoint network'

/- ============================================================
   §Ch.3 — LinearGeq propagator (tex 806–820).
   `maxContribForStat` never defined. With the stub the listing
   compiles VERBATIM (Bool-valued predicate coerces in
   Finset.filter).
   ============================================================ -/

-- DEVIATION (stub): never defined in the book.
def maxContribForStat (domain : Finset StatCombo) (slot : GearSlot)
    (stat : StatType) : Nat :=
  domain.fold max 0 (fun c => contribution slot c stat)

/-- Remove combos from slot i that can't contribute enough to stat s. -/
def linearGeqPropagate
    (domains : GearSlot → Finset StatCombo)
    (targets : StatType → Nat)
    (slot : GearSlot) : Finset StatCombo :=
  domains slot |>.filter fun combo =>
    StatType.all.all fun stat =>
      let myContrib := contribution slot combo stat
      let othersMax := (GearSlot.all.filter (· ≠ slot) |>.map fun j =>
        maxContribForStat (domains j) j stat).sum
      let infusionBudget := 90  -- 18 slots × 5 each
      myContrib + othersMax + infusionBudget ≥ targets stat

/- ============================================================
   §Ch.3 — LinearLeq propagator (tex 862–876). Same shape;
   `minContribForStat` never defined. Compiles with the stub.
   NOTE: a min-fold over a possibly-EMPTY Finset needs a neutral
   element; the book never says what minContrib of an empty
   domain is (with 0 the propagator becomes a no-op; the honest
   neutral is "no information", i.e. 0 only if the domain can be
   empty — a subtlety the monotonicity proof at tex 884–891
   silently skips: min over a smaller NONEMPTY set is ≥, but the
   sets here can become empty).
   ============================================================ -/

-- DEVIATION (stub): never defined in the book.
def minContribForStat (domain : Finset StatCombo) (slot : GearSlot)
    (stat : StatType) : Nat :=
  (domain.image (fun c => contribution slot c stat)).min.getD 0

/-- Remove combos from slot i that would force unavoidable overshoot
    on some stat beyond the allowed threshold. -/
def linearLeqPropagate
    (domains : GearSlot → Finset StatCombo)
    (targets : StatType → Nat)
    (maxOvershoot : Nat)  -- e.g., 200 stat points
    (slot : GearSlot) : Finset StatCombo :=
  domains slot |>.filter fun combo =>
    StatType.all.all fun stat =>
      let myContrib := contribution slot combo stat
      let othersMin := (GearSlot.all.filter (· ≠ slot) |>.map fun j =>
        minContribForStat (domains j) j stat).sum
      myContrib + othersMin ≤ targets stat + maxOvershoot

/- ============================================================
   §Ch.3 — Infusion budget propagator (tex 917–929): compiles
   VERBATIM given the stubs.
   ============================================================ -/

/-- Check whether the total stat deficit across all stats exceeds
    the infusion budget (18 slots × 5 = 90 points). -/
def infusionBudgetFeasible
    (domains : GearSlot → Finset StatCombo)
    (targets : StatType → Nat) : Bool :=
  let totalDeficit := StatType.all.map (fun stat =>
    let bestGear := (GearSlot.all.map fun slot =>
      maxContribForStat (domains slot) slot stat).sum
    if targets stat > bestGear then targets stat - bestGear
    else 0) |>.sum
  totalDeficit ≤ 90

/- ============================================================
   §Ch.5 — Fail-first variable selection (tex 1247–1254):
   compiles VERBATIM (given Inhabited GearSlot for `head!`,
   which the book never provides — `deriving Inhabited` is absent
   from GearSlot). NOTE: if every domain is a singleton, `unfixed`
   is empty and `head!` PANICS at runtime; the book never guards
   this.
   ============================================================ -/

/-- Select the unfixed slot with the smallest remaining domain. -/
def selectSlotFailFirst
    (domains : GearSlot → Finset StatCombo) : GearSlot :=
  let unfixed := GearSlot.all.filter fun s => (domains s).card > 1
  unfixed.foldl (init := unfixed.head!) fun best slot =>
    if (domains slot).card < (domains best).card then slot else best

/- ============================================================
   §Ch.5 — Value ordering (tex 1263–1281): compiles VERBATIM
   given the stubs (`>` coerces to Bool in `mergeSort`).
   ============================================================ -/

/-- Find the stat with the largest remaining deficit. -/
def tightestStat (domains : GearSlot → Finset StatCombo)
    (targets : StatType → Nat) : StatType :=
  StatType.all.foldl (init := .power) fun best stat =>
    let bestGear := (GearSlot.all.map fun s =>
      maxContribForStat (domains s) s stat).sum
    let deficit := if targets stat > bestGear then targets stat - bestGear else 0
    let bestDeficit := if targets best > (GearSlot.all.map fun s =>
      maxContribForStat (domains s) s best).sum then targets best - (GearSlot.all.map fun s =>
      maxContribForStat (domains s) s best).sum else 0
    if deficit > bestDeficit then stat else best

/-- Order combos by contribution to the tightest stat (descending). -/
noncomputable def orderCombos (slot : GearSlot) (combos : Finset StatCombo)
    (tightest : StatType) : List StatCombo :=
  combos.toList.mergeSort fun a b =>
    contribution slot a tightest > contribution slot b tightest
-- DEVIATION: `noncomputable` added. AS PRINTED this def fails to
-- compile: "failed to compile definition … depends on 'Finset.toList',
-- which is 'noncomputable'". Mathlib's `Finset.toList` chooses a
-- representative via `Quotient.out` — you cannot RUN code that uses it.
-- So even granting Mathlib, the book's value-ordering code cannot
-- execute; a solver would need `Finset.sort` or a list-backed domain.

/- ============================================================
   §Ch.6 — Backtracking search (tex 1334–1359).
   FAILS AS PRINTED (three errors):
   1. `(domains' s).isEmpty` — Mathlib's Finset has NO `isEmpty`:
      "Invalid field `isEmpty` … Finset". (Fixed: `= ∅` / card.)
   2. `(domains' slot).fold best fun acc combo => …` —
      `Finset.fold` is `fold (op) [Commutative op] [Associative op]
      (b) (f) (s)`: a fold over a COMMUTATIVE operation, not a
      general accumulator loop. The printed call passes the
      incumbent where the operation belongs — type error — and no
      commutative structure exists for this accumulation anyway.
      (Fixed: `.toList.foldl`.)
   3. `propagateToFixpoint`, `extractBuild`, `selectSlot`,
      `fixSlot` never defined.
   ============================================================ -/

-- DEVIATION (stubs): never defined in the book. Note that computable
-- enumeration of a `Finset` is nontrivial (`Finset.toList` is
-- noncomputable); the stub enumerates a reference list filtered by
-- (decidable) membership.
def referenceCombos : List StatCombo :=
  [⟨"Berserker's", .triple, [.power], [.precision, .ferocity]⟩,
   ⟨"Knight's",    .triple, [.toughness], [.power, .precision]⟩,
   ⟨"Marauder",    .quad, [.power, .precision], [.vitality, .ferocity]⟩,
   ⟨"Celestial",   .celestial, [], []⟩]
def enumerate (s : Finset StatCombo) : List StatCombo :=
  referenceCombos.filter (· ∈ s)
def propagateToFixpoint (d : GearSlot → Finset StatCombo)
    : GearSlot → Finset StatCombo := d
def extractBuild (_ : GearSlot → Finset StatCombo) : Build :=
  { gear := fun _ => default, rune := ⟨""⟩, infusions := fun _ => 0 }
def selectSlot (d : GearSlot → Finset StatCombo) : GearSlot :=
  selectSlotFailFirst d
def fixSlot (d : GearSlot → Finset StatCombo) (slot : GearSlot)
    (combo : StatCombo) : GearSlot → Finset StatCombo :=
  fun s => if s = slot then {combo} else d s

/-- Backtracking search with propagation at each node. -/
partial def backtrack
    (domains : GearSlot → Finset StatCombo)
    (assigned : List (GearSlot × StatCombo))
    (best : Option (Build × Nat))  -- incumbent
    (targets : StatType → Nat) : Option (Build × Nat) :=
  -- 1. Propagate
  let domains' := propagateToFixpoint domains
  -- 2. Check for empty domain (contradiction)
  if GearSlot.all.any (fun s => (domains' s).card = 0) then best
  -- DEVIATION: book has `(domains' s).isEmpty` — no such Finset field.
  -- 3. Check if all assigned
  else if GearSlot.all.all (fun s => (domains' s).card = 1) then
    let build := extractBuild domains'
    let pen := totalPenalty build targets wMiss wOver
    match best with
    | none => some (build, pen)
    | some (_, bestPen) =>
      if pen < bestPen then some (build, pen) else best
  -- 4. Branch on smallest domain (fail-first)
  else
    let slot := selectSlot domains'  -- smallest non-singleton domain
    (enumerate (domains' slot)).foldl (init := best) fun acc combo =>
      -- DEVIATION: book misuses `Finset.fold` (see header note); a
      -- straight `.toList.foldl` repair ALSO fails (`Finset.toList` is
      -- noncomputable), so the computable `enumerate` stub is used.
      let domains'' := fixSlot domains' slot combo
      backtrack domains'' ((slot, combo) :: assigned) acc targets

/- ============================================================
   §Ch.6 — A* skeleton (tex 1449–1472).
   FAILS AS PRINTED (four errors):
   1. `SearchNode … deriving Repr` — the `domains` field is a
      FUNCTION (GearSlot → Finset StatCombo); Repr cannot be
      derived for function types: "default handlers have not been
      implemented yet … deriving Repr".
   2. `BinaryHeap` — not core Lean; it is `Batteries.BinaryHeap`
      (unqualified name fails without `open Batteries`).
   3. `queue.extractMin` — BinaryHeap has only `extractMax`, and
      it returns `Option α × BinaryHeap α lt`, NOT
      `Option (α × BinaryHeap α lt)`: the printed
      `| some (node, queue')` match does not typecheck.
   4. `expandNode` never defined.
   ============================================================ -/

open Batteries

structure SearchNode where
  domains  : GearSlot → Finset StatCombo
  assigned : List (GearSlot × StatCombo)
  gCost    : Nat   -- penalty from fixed slots
  hCost    : Nat   -- LP bound on remaining
  -- DEVIATION: book adds `deriving Repr`, impossible for a
  -- function-typed field.

def SearchNode.fCost (n : SearchNode) : Nat := n.gCost + n.hCost

-- DEVIATION (stub): never defined in the book.
def expandNode (node : SearchNode)
    (queue : BinaryHeap SearchNode (·.fCost < ·.fCost))
    (incumbent : Option (Build × Nat))
    (targets : StatType → Nat) : Option (Build × Nat) :=
  incumbent

/-- A* search for the optimal gear build. -/
partial def aStarSearch
    (queue : BinaryHeap SearchNode (·.fCost < ·.fCost))
    (incumbent : Option (Build × Nat))
    (targets : StatType → Nat) : Option (Build × Nat) :=
  -- DEVIATION: `extractMin` does not exist (only `extractMax`) and it
  -- returns a PAIR of options, not an optional pair:
  match queue.extractMax with
  | (none, _) => incumbent  -- queue empty: incumbent is optimal
  | (some node, queue') =>
    -- Pruning: if f(node) ≥ incumbent, skip
    match incumbent with
    | some (_, bestPen) =>
      if node.fCost ≥ bestPen then aStarSearch queue' incumbent targets
      else expandNode node queue' incumbent targets
    | none => expandNode node queue' incumbent targets
-- NOTE: with the comparison `·.fCost < ·.fCost`, `extractMax` pops the
-- LARGEST fCost — a max-heap. Best-first search needs the SMALLEST f.
-- The printed code (even repaired) explores worst-first unless the
-- comparison is flipped. The book never mentions this.

/- ============================================================
   §Ch.7 — Reduced-cost fixing (tex 1655–1667): compiles given a
   stub `LPResult` (never defined; needs `reducedCost` and
   `objectiveValue` fields of Float).
   ============================================================ -/

-- DEVIATION (stub): never defined in the book.
structure LPResult where
  objectiveValue : Float
  reducedCost    : GearSlot → StatCombo → Float

/-- Remove combos whose reduced cost proves they can't be in
    any solution better than the incumbent. -/
def reducedCostFix
    (domains : GearSlot → Finset StatCombo)
    (lpResult : LPResult)
    (incumbentPen : Nat) : GearSlot → Finset StatCombo :=
  fun slot => (domains slot).filter fun combo =>
    let rc := lpResult.reducedCost slot combo
    -- Keep combo only if LP bound + reduced cost < incumbent
    lpResult.objectiveValue + rc < incumbentPen.toFloat

/- ============================================================
   §Ch.8 — Simulated annealing driver (tex 1863–1880).
   (The single `saStep` is verified in the core file, where its
   Nat→Float coercion error is recorded.)
   FAILS AS PRINTED:
   1. `randomFeasibleBuild` never defined.
   2. Final `|>.map fun (_, _, best, bestPen, _, _) => (best, bestPen)`
      — `Prod.map` takes TWO functions; a single 6-tuple lambda is a
      type error. (Fixed with a `match`.)
   ============================================================ -/

-- Stubs for the random helpers (mirroring the core file).
def randomFeasibleBuild (_ : GearSlot → Finset StatCombo)
    (rng : StdGen) : Build × StdGen := (default, rng)   -- DEVIATION (stub)
def saStep (current : Build) (currentPen : Nat) (_temp : Float)
    (rng : StdGen) (_targets : StatType → Nat)
    : Build × Nat × StdGen := (current, currentPen, rng) -- DEVIATION (stub;
    -- the real saStep, with its own recorded error, is in the core file)

/-- Full simulated annealing run. -/
def simulatedAnnealing (domains : GearSlot → Finset StatCombo)
    (targets : StatType → Nat) (rng : StdGen)
    (maxIters : Nat := 10000) : Build × Nat :=
  let (init, rng) := randomFeasibleBuild domains rng
  let initPen := totalPenalty init targets wMiss wOver
  let t0 : Float := 448.0    -- initial temperature
  let alpha : Float := 0.997  -- cooling rate
  let r := (List.range maxIters).foldl
    (init := (init, initPen, init, initPen, t0, rng))
    fun (current, currentPen, best, bestPen, temp, rng) _ =>
      let (current', pen', rng') := saStep current currentPen temp rng targets
      let temp' := alpha * temp
      let (best', bestPen') :=
        if pen' < bestPen then (current', pen') else (best, bestPen)
      (current', pen', best', bestPen', temp', rng')
  match r with
  | (_, _, best, bestPen, _, _) => (best, bestPen)
  -- DEVIATION: book ends with `|>.map fun (_, _, best, bestPen, _, _) =>`
  -- — `Prod.map` takes two functions; type error as printed.

/- ============================================================
   §Ch.11 — The complete solver (tex 2313–2360).
   FAILS AS PRINTED (five errors — this is the book's headline
   listing):
   1. `simulatedAnnealing domains problem.targets` — MISSING the
      `rng` argument (only `maxIters` has a default): "function
      expected … / type mismatch".
   2. `let warmBuild := simulatedAnnealing …` returns
      `Build × Nat`, but the next line calls
      `totalPenalty warmBuild …` — a PAIR where a Build is
      expected: type error (and the pair already contains the
      penalty).
   3. `anyDomainEmpty`, `allSingleton`, `gearStats`,
      `solveLPRelaxation`, `smallestDomainSlot`, `infusionDP`
      never defined (in scope).
   4. `(domains slot).fold incumbent fun best combo => …` — same
      `Finset.fold` misuse as backtrack.
   5. The `else` branch of `branchAndBound` produces
      `Build × Nat`, but the declared result is
      `Option (Build × Nat)` — missing `some`.
   SEMANTIC NOTE (REVIEW.md): `branchAndBound` NEVER returns
   `none`, so `solve`'s `| none => .infeasible` arm is dead code —
   the printed solver cannot ever report infeasibility from B&B.
   ============================================================ -/

inductive SolverResult where
  | optimal    : Build → Nat → SolverResult   -- build + penalty
  | infeasible : SolverResult

structure GearProblem where            -- DEVIATION (stub): never defined
  targets        : StatType → Nat
  initialDomains : GearSlot → Finset StatCombo
  wMissPerStat   : StatType → Nat := fun _ => wMiss  -- Ch.14 sweep field

-- DEVIATION (stubs): never defined in the book.
def anyDomainEmpty (d : GearSlot → Finset StatCombo) : Bool :=
  GearSlot.all.any fun s => (d s).card = 0
def allSingleton (d : GearSlot → Finset StatCombo) : Bool :=
  GearSlot.all.all fun s => (d s).card = 1
def gearStats (b : Build) : StatType → Nat := fun s =>
  (GearSlot.all.map fun slot => contribution slot (b.gear slot) s).sum
def solveLPRelaxation (_ : GearSlot → Finset StatCombo)
    (_ : StatType → Nat) : Nat := 0
def smallestDomainSlot (d : GearSlot → Finset StatCombo) : GearSlot :=
  selectSlotFailFirst d
def infusionDP (_gearStats : StatType → Nat)
    (_targets : StatType → Nat) (_budget : Nat := 18)
    : StatType → Nat := fun _ => 0
  -- (repaired executable version lives in the core file)

/-- Does the build meet every HARD stat floor? (the solver's contract) -/
def meetsFloors (b : Build) (targets : StatType → Nat) : Bool :=
  StatType.all.all fun s => targets s ≤ statTotal b s

/-- Branch and bound with propagation + LP bounding at each node.
    RECONCILED to the hard-floor model: the incumbent is an `Option`
    (`none` = "no floor-meeting build found yet"), a leaf is accepted only
    after `meetsFloors`, and `none` genuinely reports infeasibility — so
    `solve`'s `.infeasible` arm is now LIVE, not dead code. -/
partial def branchAndBound
    (domains : GearSlot → Finset StatCombo)
    (targets : StatType → Nat)
    (incumbent : Option (Build × Nat))
    : Option (Build × Nat) :=
  let domains := propagateToFixpoint domains
  if anyDomainEmpty domains then incumbent      -- dead subtree
  else if allSingleton domains then
    let build := extractBuild domains
    let full := { build with infusions := infusionDP (gearStats build) targets }
    if meetsFloors full targets then
      let pen := totalPenalty full targets wMiss wOver
      match incumbent with
      | none          => some (full, pen)
      | some (_, best) => if pen < best then some (full, pen) else incumbent
    else incumbent                              -- leaf misses a floor: reject
  else
    let pruned := match incumbent with
      | some (_, best) => decide (solveLPRelaxation domains targets ≥ best)
      | none           => false
    if pruned then incumbent
    else
      let slot := smallestDomainSlot domains
      (enumerate (domains slot)).foldl (init := incumbent) fun best combo =>
        branchAndBound (fixSlot domains slot combo) targets best

def solve (problem : GearProblem) : SolverResult :=
  -- Phase 1: Initial propagation
  let domains := propagateToFixpoint problem.initialDomains
  if anyDomainEmpty domains then .infeasible
  else
  -- Phase 2: Warm start (SA); adopt it ONLY if it meets the hard floors.
  let (warm, _) := simulatedAnnealing domains problem.targets (mkStdGen 0)
  let warmInc : Option (Build × Nat) :=
    if meetsFloors warm problem.targets
    then some (warm, totalPenalty warm problem.targets wMiss wOver)
    else none
  -- Phase 3: Branch and bound
  match branchAndBound domains problem.targets warmInc with
  | none              => .infeasible   -- LIVE: no floor-meeting build exists
  | some (build, pen) => .optimal build pen

/- ============================================================
   §Ch.12 — Propagation soundness (tex 2419–2446).
   `linearGeq_sound` elaborates (book's own sorry) — but the
   STATEMENT is wrong: it concludes `statTotal b s + 90 < targets s`,
   yet `statTotal` already includes the build's infusions (up to
   90 points). From the removal condition one can only conclude
   `statTotal b s < targets s`. As stated the theorem is FALSE
   (take b with all 18 infusions on s). See REVIEW.md.
   `propagation_preserves_optimal` FAILS AS PRINTED: it applies
   `isOptimal problem b_opt` where `isOptimal` (tex 666) takes an
   `OptProblem` and a `Solution P` — `b_opt : Build` is not a
   `Solution`; and `problem` is a dangling auto-bound variable.
   (Repaired with a Build-level optimality predicate.) It is ALSO
   mathematically FALSE for the book's soft-penalty objective
   (LinearGeq can prune the true optimum — see REVIEW.md).
   ============================================================ -/

/-- CORRECTED statement (REVIEW.md #4): if LinearGeq removes combo `c`
    from slot `i`, then ANY build that (a) uses `c` on slot `i`, (b) draws
    its other gear from the same domains, and (c) respects the 18-infusion
    budget, FAILS some stat floor: `∃ s, statTotal b s < targets s`.
    The book's printed `+ 90` conclusion double-counts the infusions
    (`statTotal` already includes up to 5·18 = 90 infusion points), and it
    omitted hypotheses (b)/(c), so it was false as printed. This corrected
    form is a NECESSARY condition for hard-floor feasibility, hence the
    honest justification for LinearGeq pruning. -/
theorem linearGeq_sound
    (domains : GearSlot → Finset StatCombo)
    (targets : StatType → Nat)
    (slot : GearSlot) (combo : StatCombo)
    (h_removed : combo ∉ linearGeqPropagate domains targets slot)
    (h_was_in : combo ∈ domains slot)
    (b : Build) (h_uses : b.gear slot = combo)
    (h_others : ∀ j, b.gear j ∈ domains j)
    (h_budget : (StatType.all.map b.infusions).sum ≤ 18) :
    ∃ s : StatType, statTotal b s < targets s := by
  -- h_removed gives ∃ s, contribution(i,c,s) + othersMax(s) + 90 < T(s).
  -- statTotal b s = contribution(i,c,s) + Σ_{j≠i} contribution(j,·,s)
  --                 + 5·infusions s
  --              ≤ contribution(i,c,s) + othersMax(s) + 90 < T(s).
  sorry -- HONEST SPECIFICATION (proof left as an extended exercise):
        -- needs maxContribForStat as an upper bound on the domain and
        -- monotonicity of Finset/List sums.

/-- Propagation to fixpoint preserves every FEASIBLE build (one meeting
    all hard floors within the domains and budget). This is the honest,
    TRUE restatement (REVIEW.md #1): LinearGeq only removes combos that
    make some floor unreachable, so a build meeting all floors keeps all
    its combos. It REPLACES the book's false
    `propagation_preserves_optimal`, which claimed the soft-penalty
    optimum survives — LinearGeq can prune that optimum. -/
theorem propagation_preserves_feasible
    (domains₀ : GearSlot → Finset StatCombo)
    (targets : StatType → Nat)
    (b : Build)
    (h_floors : ∀ s, statTotal b s ≥ targets s)   -- meets every hard floor
    (h_budget : (StatType.all.map b.infusions).sum ≤ 18)
    (h_in : ∀ s, b.gear s ∈ domains₀ s) :
    let domains' := propagateToFixpoint domains₀
    ∀ s, b.gear s ∈ domains' s := by
  -- By induction on propagation steps: by linearGeq_sound, any removed
  -- combo would force a floor miss, contradicting h_floors.
  sorry -- HONEST SPECIFICATION (proof left as an extended exercise).

/- ============================================================
   §Ch.12 — LP bound validity (tex 2473–2483): elaborates given a
   stub `BBNode` (never defined; needs Finset domains + targets).
   ============================================================ -/

-- DEVIATION (stub): never defined in the book.
structure BBNode where
  domains : GearSlot → Finset StatCombo
  targets : StatType → Nat

-- DEVIATION (stub): Float-valued LP solver interface, never defined.
def solveLPRelaxationF (_ : GearSlot → Finset StatCombo)
    (_ : StatType → Nat) : LPResult := ⟨0.0, fun _ _ => 0.0⟩

/-- The LP relaxation value is a lower bound on any integer solution. -/
theorem lp_bound_valid
    (node : BBNode)
    (lpResult : LPResult)
    (h_lp : lpResult = solveLPRelaxationF node.domains node.targets)
    -- DEVIATION: book writes `solveLPRelaxation`, whose only prior use
    -- (tex 2350) returns a bare bound, not a record with
    -- `.objectiveValue` — the two solver interfaces are inconsistent.
    (b : Build)
    (h_feasible : ∀ s, b.gear s ∈ node.domains s) :
    lpResult.objectiveValue ≤ (totalPenalty b node.targets wMiss wOver).toFloat := by
  -- The build b corresponds to a 0-1 assignment, which is feasible for the LP
  -- The LP optimum ≤ any feasible LP solution
  sorry -- BOOK'S OWN SORRY

/- ============================================================
   §Ch.12 — Composing the full proof (tex 2602–2630).
   FAILS AS PRINTED, irreparably short of rewriting:
   * `unfold solve` followed by bullets `·` — `unfold` produces ONE
     goal; there is no case split, so the first bullet fails with
     "no goals to prove" / "unexpected bullet".
   * `intro b hfeas` in "case 1" — the goal is a `match`, not an
     implication, until `split` is used (the book never introduces
     `split`).
   * `propagation_preserves_optimal ..`, `domain_empty ..`,
     `extractBuild_feasible ..`, `bb_invariant_at_termination ..`,
     `queue_empty ..` — four of these five lemma names are NEVER
     defined anywhere ("Unknown identifier").
   * `build.feasible problem` — `Build.feasible` never defined.
   We record the statement with a sorry; the printed proof body is
   pseudo-Lean and cannot be salvaged minimally.
   ============================================================ -/

-- MODELLING RECONCILIATION (matches OptimizationVerification.lean):
-- feasibility includes the HARD stat floors, so the solver soundness
-- theorem below is true-in-principle and matches what `solve` computes.
def Build.feasible (b : Build) (p : GearProblem) : Prop :=
  (∀ slot, b.gear slot ∈ p.initialDomains slot) ∧
  ((StatType.all.map b.infusions).sum = 18) ∧
  (∀ s, statTotal b s ≥ p.targets s)   -- HARD stat floors

/-- The complete solver soundness theorem. -/
theorem solver_sound_proof (problem : GearProblem) :
    match solve problem with
    | .optimal build pen =>
        build.feasible problem ∧
        pen = totalPenalty build problem.targets wMiss wOver ∧
        ∀ b, b.feasible problem →
          totalPenalty b problem.targets wMiss wOver ≥ pen
    | .infeasible =>
        ∀ b : Build, ¬ b.feasible problem := by
  sorry -- HONEST SPECIFICATION (proof left as an extended exercise).
        -- The book's printed tactic proof (tex 2613–2630) was pseudo-code
        -- that did not elaborate. With the hard-floor `feasible` above the
        -- statement is no longer false (REVIEW.md #1/#2 reconciled); a real
        -- proof composes linearGeq_sound + propagation_preserves_feasible
        -- + lp_bound_valid + bb_step_preserves.

/- ============================================================
   §Ch.14 — What-if mode (tex 2959–2973): compiles VERBATIM given
   a stub `berserkers` (never defined as a Lean value).
   ============================================================ -/

-- DEVIATION (stub): never defined in the book.
def berserkers : StatCombo :=
  ⟨"Berserker's", .triple, [.power], [.precision, .ferocity]⟩

/-- Fix specific slots to specific combos before solving. -/
def applyWhatIf (domains : GearSlot → Finset StatCombo)
    (fixed : List (GearSlot × StatCombo))
    : GearSlot → Finset StatCombo :=
  fun slot =>
    match fixed.find? (fun (s, _) => s == slot) with
    | some (_, combo) => {combo}  -- singleton domain
    | none => domains slot

-- Example: "I have Legendary Berserker armour"
def legendaryBerserkerArmour : List (GearSlot × StatCombo) :=
  [(.headgear, berserkers), (.shoulders, berserkers),
   (.coat, berserkers), (.gloves, berserkers),
   (.leggings, berserkers), (.boots, berserkers)]

end VOM
