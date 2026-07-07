/- ============================================================
   Verification file for "Verified Optimization: From Lattices
   to Solvers in Lean 4" (verified-optimization.tex, 3199 lines)

   Environment: CORE LEAN ONLY, toolchain leanprover/lean4:v4.31.0
   (no packages). Listings that require Mathlib (`Finset`,
   `SemilatticeSup`, `BinaryHeap`) are verified separately in
   OptimizationMathlibVerification.lean — the book NEVER declares
   this dependency.

   Conventions:
     -- DEVIATION (stub): helper the book references but never
        defines; minimal definition supplied so listings elaborate.
     -- DEVIATION: printed code fails to compile; the exact error
        is recorded in a comment and a minimal fix applied.
     -- BOOK'S OWN SORRY: a `sorry` the book prints deliberately.

   Line numbers refer to verified-optimization.tex.
   ============================================================ -/

set_option linter.unusedVariables false

namespace VO

/- ============================================================
   §Ch.1 — Core data model (tex 378–401): compiles VERBATIM.
   ============================================================ -/

inductive StatType where
  | power | precision | ferocity | toughness | vitality
  | conditionDamage | expertise | concentration | healingPower
  deriving DecidableEq, Repr, Hashable

inductive GearSlot where
  | headgear | shoulders | coat | gloves | leggings | boots
  | mainhand | offhand    -- or combined as twoHand
  | amulet | ring1 | ring2 | accessory1 | accessory2 | backPiece
  deriving DecidableEq, Repr

inductive ComboCategory where
  | triple   -- 1 major, 2 minor
  | quad     -- 2 major, 2 minor
  | celestial -- 7 equal
  deriving DecidableEq, Repr

structure StatCombo where
  name     : String
  category : ComboCategory
  majors   : List StatType
  minors   : List StatType
  deriving DecidableEq, Repr

/- ============================================================
   §Ch.1 — Coefficients and contribution (tex 410–453):
   compiles VERBATIM.
   ============================================================ -/

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
  | .mainhand   => ⟨125, 90,  108, 59, 59⟩  -- 1H
  | .offhand    => ⟨125, 90,  108, 59, 59⟩  -- 1H
  | .amulet     => ⟨157, 108, 133, 71, 72⟩
  | .ring1      => ⟨126, 85,  106, 56, 57⟩
  | .ring2      => ⟨126, 85,  106, 56, 57⟩
  | .accessory1 => ⟨110, 74,  92,  49, 50⟩
  | .accessory2 => ⟨110, 74,  92,  49, 50⟩
  | .backPiece  => ⟨63,  40,  52,  27, 28⟩

/-- Contribution of `combo` on `slot` to `stat`. -/
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

/- ============================================================
   §Ch.1 — Build and statTotal (tex 460–472).
   FAILS AS PRINTED: `Rune` is referenced ("to be defined later")
   but is NEVER defined anywhere in the book; `GearSlot.all` is
   never defined either.  Errors: "Unknown identifier `Rune`",
   "Unknown constant `GearSlot.all`".
   ============================================================ -/

-- DEVIATION (stub): the book promises to define `Rune` later and never does.
structure Rune where
  name : String
  deriving DecidableEq, Repr

-- DEVIATION (stub): `GearSlot.all` never defined in the book.
def GearSlot.all : List GearSlot :=
  [.headgear, .shoulders, .coat, .gloves, .leggings, .boots,
   .mainhand, .offhand,
   .amulet, .ring1, .ring2, .accessory1, .accessory2, .backPiece]

-- DEVIATION (stub): `StatType.all` never defined in the book.
def StatType.all : List StatType :=
  [.power, .precision, .ferocity, .toughness, .vitality,
   .conditionDamage, .expertise, .concentration, .healingPower]

structure Build where
  gear      : GearSlot → StatCombo
  rune      : Rune   -- to be defined later
  infusions : StatType → Nat
  -- Invariant: ∑ infusions = 18

/-- Total stat from gear + infusions (excluding base stats and buffs). -/
def statTotal (b : Build) (s : StatType) : Nat :=
  let gearTotal := (GearSlot.all.map fun slot =>
    contribution slot (b.gear slot) s).sum
  gearTotal + 5 * b.infusions s

/- ============================================================
   §Ch.1 — Penalty (tex 491–503): compiles given the stubs.
   ============================================================ -/

def penalty (target actual : Nat) (wMiss wOver : Nat) : Nat :=
  if actual < target then
    wMiss * (target - actual)
  else
    wOver * (actual - target)

def totalPenalty (b : Build) (targets : StatType → Nat)
    (wMiss wOver : Nat) : Nat :=
  (StatType.all.map fun s =>
    penalty (targets s) (statTotal b s) wMiss wOver).sum

-- DEVIATION (stub): several later listings use free variables
-- `wMiss`/`wOver` as if they were global constants (tex 1348, 1767,
-- 1787, 1852, 1976, 2324, 2345...). The book never fixes them.
def wMiss : Nat := 10
def wOver : Nat := 1

/- ============================================================
   §Ch.2 — OptProblem (tex 657–668): compiles VERBATIM
   (relies on auto-bound implicits for V, D).
   NOTE: the prose Definition box says the objective maps to ℝ;
   the Lean uses Int. Core Lean has no Real, so Int is the honest
   choice, but the mismatch is never acknowledged.
   ============================================================ -/

structure OptProblem (V : Type) (D : V → Type) where
  constraints : (∀ v, D v) → Prop
  objective   : (∀ v, D v) → Int

structure Solution (P : OptProblem V D) where
  assignment : ∀ v, D v
  feasible   : P.constraints assignment

def isOptimal (P : OptProblem V D) (sol : Solution P) : Prop :=
  ∀ other : Solution P, P.objective sol.assignment ≤ P.objective other.assignment

/- ============================================================
   §Ch.3 — Cell / runToFixpoint (tex 570–586) uses
   `SemilatticeSup` and `⊔`: NOT in core Lean (Mathlib order
   classes). Verified in OptimizationMathlibVerification.lean.
   The three propagators (tex 806–929) use `Finset`: also
   Mathlib-only. See the Mathlib file.
   ============================================================ -/

/- ============================================================
   §Ch.4 — Simplex sketch (tex 1041–1066).
   All four helpers (`minRatioTest`, `gaussianPivot`,
   `blandEnteringVariable`, `extractSolution`) and the type
   `SimplexResult` are never defined. With stubs the listing
   compiles.
   ============================================================ -/

structure Tableau where
  m : Nat  -- number of constraints
  n : Nat  -- number of variables
  tab : Array (Array Float)  -- (m+1) × (n+m+1) augmented matrix
  basis : Array Nat          -- indices of basic variables

-- DEVIATION (stubs): never defined in the book.
inductive SimplexResult where
  | optimal   : Array Float → SimplexResult
  | unbounded : SimplexResult
instance : Inhabited SimplexResult := ⟨.unbounded⟩
def minRatioTest (_ : Tableau) (_ : Nat) : Option Nat := none
def gaussianPivot (T : Tableau) (_ _ : Nat) : Tableau := T
def blandEnteringVariable (_ : Tableau) : Option Nat := none
def extractSolution (_ : Tableau) : Array Float := #[]

/-- One pivot step: bring variable enterIdx into the basis. -/
def pivot (T : Tableau) (enterIdx : Nat) : Option Tableau :=
  -- Minimum ratio test to find the leaving variable
  let leaveIdx? := minRatioTest T enterIdx
  match leaveIdx? with
  | none => none  -- unbounded
  | some leaveIdx =>
    -- Gaussian elimination to pivot
    some (gaussianPivot T enterIdx leaveIdx)

/-- Run simplex to completion. -/
partial def simplex (T : Tableau) : SimplexResult :=
  match blandEnteringVariable T with
  | none => .optimal (extractSolution T)  -- no improving variable
  | some enterIdx =>
    match pivot T enterIdx with
    | none => .unbounded
    | some T' => simplex T'

/- ============================================================
   §Ch.5 — Symmetry breaking (tex 1300–1312).
   `comboOrd` never defined. `sorry` is the book's own.
   ============================================================ -/

-- DEVIATION (stub): `comboOrd` never defined in the book.
def comboOrd (c : StatCombo) : Nat := c.name.length

/-- A build is canonical if symmetric slot pairs are ordered. -/
def Build.isCanonical (b : Build) : Prop :=
  comboOrd (b.gear .ring1) ≤ comboOrd (b.gear .ring2) ∧
  comboOrd (b.gear .accessory1) ≤ comboOrd (b.gear .accessory2)

/-- Every build has a canonical equivalent with the same penalty. -/
theorem canonical_exists (b : Build) :
    ∃ b', b'.isCanonical ∧ totalPenalty b' = totalPenalty b := by
  -- Swap rings/accessories if needed; stat totals are unchanged
  -- since contribution depends only on the slot type, not the index
  sorry -- BOOK'S OWN SORRY ("exercise for the reader")

/- ============================================================
   §Ch.6 — Nogood store (tex 1503–1525): compiles VERBATIM.
   *** LOGIC BUG (see REVIEW.md): `extractNogood` keeps the
   assignments that contributed POSITIVELY to the failed stat.
   For a stat-floor (Geq) failure the culprits are the slots that
   contributed too LITTLE; the extracted set is not a valid
   nogood (it is not provably inconsistent). ***
   ============================================================ -/

/-- A nogood is a set of (slot, combo) assignments known to be infeasible. -/
structure Nogood where
  assignments : List (GearSlot × StatCombo)

/-- Check if the current assignment contains any known nogood. -/
def isNogoodHit (nogoods : List Nogood) (assigned : List (GearSlot × StatCombo))
    : Bool :=
  nogoods.any fun ng =>
    ng.assignments.all fun (slot, combo) =>
      assigned.any fun (s, c) => s == slot && c == combo

/-- Extract a nogood from a failed propagation.
    Analyse which assignments contributed to the empty domain. -/
def extractNogood (assigned : List (GearSlot × StatCombo))
    (failedSlot : GearSlot) (failedStat : StatType)
    : Nogood :=
  -- Keep only assignments whose contribution to failedStat
  -- was necessary for the failure
  let relevant := assigned.filter fun (slot, combo) =>
    contribution slot combo failedStat > 0
  ⟨relevant⟩

/- ============================================================
   §Ch.7 — Subgradient method (tex 1604–1628).
   FAILS AS PRINTED (five distinct errors):
   1. `armourSlots.pairs` — no `List.pairs` in core Lean (or
      Batteries/Mathlib): "Unknown constant `List.pairs`".
   2. `lambda.zipWith violations.toArray fun li gi => ...` —
      in v4.31 `Array.zipWith` takes the function FIRST
      (`zipWith f as bs`); the printed argument order gives
      "Application type mismatch: argument ... expected to have
      type ?m → ?m → ?m".
   3. `Float.max` — "Unknown constant `Float.max`" (use `max`).
   4. `Array.mkArray` — removed in v4.31 ("Unknown constant";
      renamed `Array.replicate`).
   5. `lagrangianDual`: foldl accumulator is a 3-tuple but the
      declared result type is a pair, and `|>.map fun (bound, _, sol)
      => ...` — `Prod.map` takes TWO functions, so this is a type
      error; `none` also needs an ascription.
   Also `runeOf : StatCombo → Rune` is conceptually wrong: a stat
   combo does not determine a rune (see REVIEW.md).
   ============================================================ -/

-- DEVIATION (stubs): never defined in the book.
def List.pairs : List α → List (α × α)
  | [] => []
  | x :: xs => (xs.map fun y => (x, y)) ++ pairs xs
def runeOf (_ : StatCombo) : Rune := ⟨"?"⟩

structure GearProblem where            -- DEVIATION (stub): never defined
  targets        : StatType → Nat
  initialDomains : GearSlot → List StatCombo
  wMissPerStat   : StatType → Nat := fun _ => 50   -- see tex 3009 drift

def solveRelaxedPerSlot (_ : Array Float) (_ : StatType → Nat)
    : GearSlot → StatCombo := fun _ => ⟨"Berserker's", .triple,
      [.power], [.precision, .ferocity]⟩            -- DEVIATION (stub)
def lagrangianObjective (_ : GearSlot → StatCombo) (_ : Array Float)
    (_ : StatType → Nat) : Float := 0.0             -- DEVIATION (stub)
def defaultSolution : GearSlot → StatCombo :=
  solveRelaxedPerSlot #[] (fun _ => 0)              -- DEVIATION (stub)

/-- One iteration of subgradient optimisation. -/
def subgradientStep (lambda : Array Float) (stepSize : Float)
    (solution : GearSlot → StatCombo) : Array Float :=
  -- Subgradient: violation of the rune constraint
  -- g_ij = 1 if rune(i) ≠ rune(j), else 0
  let armourSlots : List GearSlot :=   -- DEVIATION: book omits ascription; bare
    [.headgear, .shoulders, .coat, .gloves, .leggings, .boots]  -- list elaborates, kept
  let violations := (List.pairs armourSlots).map fun (i, j) =>
    if runeOf (solution i) == runeOf (solution j) then 0.0 else 1.0
  -- Update: λ' = max(0, λ + stepSize * g)
  -- DEVIATION: `lambda.zipWith violations.toArray fun li gi =>` has the
  -- v4.31 argument order wrong, and `Float.max` does not exist:
  Array.zipWith (fun li gi => max 0.0 (li + stepSize * gi))
    lambda violations.toArray

/-- Run the subgradient method for a fixed number of iterations. -/
def lagrangianDual (problem : GearProblem) (iters : Nat := 100)
    : Float × (GearSlot → StatCombo) :=
  let init_lambda := Array.replicate 15 0.0  -- C(6,2) = 15 pairs
  -- DEVIATION: book writes `Array.mkArray` (removed in v4.31) and ends with
  -- `|>.map fun (bound, _, sol) => ...` (Prod.map needs two functions);
  -- rewritten with a match. `none` needed a type ascription.
  let result := (List.range iters).foldl
    (init := ((0.0 : Float), init_lambda,
              (none : Option (GearSlot → StatCombo))))
    fun (bestBound, lambda, _bestSol) k =>
      -- Solve Lagrangian subproblem (per-slot enumeration)
      let solution := solveRelaxedPerSlot lambda problem.targets
      let bound := lagrangianObjective solution lambda problem.targets
      -- FIXED (REVIEW.md #5): diminishing step uses the CURRENT index k,
      -- so t_k → 0 as k grows. The book previously used `iters` (the fixed
      -- total), making the step CONSTANT — contradicting "diminishing".
      let stepSize := 1.0 / (1.0 + k.toFloat)
      let lambda' := subgradientStep lambda stepSize solution
      let bestBound' := max bestBound bound
      (bestBound', lambda', some solution)
  match result with
  | (bound, _, sol) => (bound, sol.getD defaultSolution)

/- ============================================================
   §Ch.8 — Neighbourhood (tex 1749–1768).
   FAILS AS PRINTED: `GearSlot.all.bind` — `List.bind` was removed
   in v4.31 ("Unknown constant `List.bind`", now `flatMap`), and
   `allCombos` is never defined.
   ============================================================ -/

-- DEVIATION (stub): `allCombos` never defined in the book
-- (Appendix A lists 41 combos in prose, not code — and the book
-- elsewhere claims there are 40).
def allCombos : List StatCombo :=
  [⟨"Berserker's", .triple, [.power], [.precision, .ferocity]⟩,
   ⟨"Knight's",    .triple, [.toughness], [.power, .precision]⟩,
   ⟨"Marauder",    .quad, [.power, .precision], [.vitality, .ferocity]⟩,
   ⟨"Minstrel's",  .quad, [.toughness, .healingPower], [.vitality, .concentration]⟩,
   ⟨"Celestial",   .celestial, [], []⟩]

/-- Generate all single-slot neighbours of a build. -/
def allNeighbours (b : Build) : List Build :=
  GearSlot.all.flatMap fun slot =>   -- DEVIATION: book has `.bind` (removed in v4.31)
    allCombos.filter (· ≠ b.gear slot) |>.map fun combo =>
      { b with gear := fun s => if s == slot then combo else b.gear s }

/-- A neighbour move: which slot changed and to what. -/
structure Move where
  slot  : GearSlot
  combo : StatCombo

/-- Generate all moves with their resulting penalties (for sorting). -/
def allMoves (b : Build) (targets : StatType → Nat)
    : List (Move × Nat) :=
  GearSlot.all.flatMap fun slot =>   -- DEVIATION: `.bind` removed in v4.31
    allCombos.filter (· ≠ b.gear slot) |>.map fun combo =>
      let b' := { b with gear := fun s =>
        if s == slot then combo else b.gear s }
      (⟨slot, combo⟩, totalPenalty b' targets wMiss wOver)

/- ============================================================
   §Ch.8 — Hill climbing (tex 1781–1803).
   `hillClimb` compiles (needs an Inhabited Build for `partial`).
   `hillClimbRestarts` FAILS AS PRINTED (three errors):
   1. `Nat.max` used as a sentinel value — it is a FUNCTION
      `Nat → Nat → Nat`, not a maximal element; Nat has no maximum.
      Error: type mismatch in the tuple.
   2. The foldl accumulator is a 3-tuple (build, pen, rng) but the
      declared return type is `Build × Nat`; `|>.fst` projects only
      the Build. Error: type mismatch at `.fst`.
   3. `defaultBuild`, `randomBuild` never defined.
   ============================================================ -/

-- DEVIATION (stubs)
instance : Inhabited StatCombo := ⟨⟨"", .triple, [], []⟩⟩
instance : Inhabited Build := ⟨⟨fun _ => default, ⟨""⟩, fun _ => 0⟩⟩
def defaultBuild : Build := default
def randomBuild (rng : StdGen) : Build × StdGen := (default, rng)

/-- Hill climbing: greedily move to the best neighbour. -/
partial def hillClimb (current : Build) (currentPen : Nat)
    (targets : StatType → Nat) : Build × Nat :=
  let neighbours := allNeighbours current
  let (bestNeigh, bestPen) := neighbours.foldl
    (init := (current, currentPen)) fun (best, bestPen) neigh =>
      let pen := totalPenalty neigh targets wMiss wOver
      if pen < bestPen then (neigh, pen) else (best, bestPen)
  if bestPen < currentPen then hillClimb bestNeigh bestPen targets
  else (current, currentPen)  -- local optimum

/-- Restart hill climbing multiple times, keep the best. -/
def hillClimbRestarts (nRestarts : Nat) (rng : StdGen)
    (targets : StatType → Nat) : Build × Nat :=
  let r := (List.range nRestarts).foldl
    (init := (defaultBuild, 1000000000, rng))
    -- DEVIATION: book's sentinel is `Nat.max`, which is the binary max
    -- FUNCTION (type error); replaced by a large literal.
    fun (best, bestPen, rng) _ =>
      let (init, rng) := randomBuild rng
      let initPen := totalPenalty init targets wMiss wOver
      let (local_, localPen) := hillClimb init initPen targets
      -- DEVIATION: book names this binder `local`, a reserved keyword
      -- in Lean 4 ("expected identifier"); renamed `local_`.
      if localPen < bestPen then (local_, localPen, rng)
      else (best, bestPen, rng)
  (r.1, r.2.1)
  -- DEVIATION: book ends with `|>.fst`, which returns only `Build`,
  -- not the declared `Build × Nat`.

/- ============================================================
   §Ch.8 — Simulated annealing step (tex 1844–1861).
   FAILS AS PRINTED:
   1. `randomSlot`, `randomCombo`, `availableCombos`, `randomFloat`
      never defined.
   2. `let delta := (neighPen - currentPen : Float)` — no Nat→Float
      coercion in core Lean: "Type mismatch: a - b has type Nat but
      is expected to have type Float".
   (The full `simulatedAnnealing` driver takes `Finset` domains —
   verified in the Mathlib file, where its own errors are recorded.)
   ============================================================ -/

-- DEVIATION (stubs)
instance : Inhabited GearSlot := ⟨.headgear⟩
def randomSlot (rng : StdGen) : GearSlot × StdGen :=
  let (n, rng') := randNat rng 0 (GearSlot.all.length - 1)
  (GearSlot.all[n % GearSlot.all.length]!, rng')
def availableCombos (_ : GearSlot) : List StatCombo := allCombos
def randomCombo (rng : StdGen) (cs : List StatCombo) : StatCombo × StdGen :=
  let (n, rng') := randNat rng 0 (cs.length - 1)
  (cs[n % cs.length]!, rng')
def randomFloat (rng : StdGen) : Float × StdGen :=
  let (n, rng') := randNat rng 0 999999
  (n.toFloat / 1000000.0, rng')

/-- One step of simulated annealing. -/
def saStep (current : Build) (currentPen : Nat) (temp : Float)
    (rng : StdGen) (targets : StatType → Nat)
    : Build × Nat × StdGen :=
  -- Pick a random neighbour (random slot, random combo)
  let (slot, rng) := randomSlot rng
  let (combo, rng) := randomCombo rng (availableCombos slot)
  let neighbour := { current with gear := fun s =>
    if s == slot then combo else current.gear s }
  let neighPen := totalPenalty neighbour targets wMiss wOver
  if neighPen ≤ currentPen then
    (neighbour, neighPen, rng)  -- always accept improvements
  else
    let delta := (neighPen - currentPen).toFloat
    -- DEVIATION: book writes `(neighPen - currentPen : Float)`,
    -- which does not typecheck in core Lean (no Nat→Float coercion).
    let (r, rng) := randomFloat rng  -- r ∈ [0, 1)
    if r < Float.exp (-delta / temp) then
      (neighbour, neighPen, rng)  -- accept with probability
    else
      (current, currentPen, rng)  -- reject

/- ============================================================
   §Ch.8 — Tabu search (tex 1903–1931).
   FAILS AS PRINTED:
   1. `Nat.max` sentinel again (function, not a value).
   2. `allNeighbourMoves`, `defaultCombo`, `setBuildSlot` never
      defined.
   Note also: the comment "OR if it produces a new global best"
   (aspiration criterion) is NOT implemented by the code.
   ============================================================ -/

-- DEVIATION (stubs)
def allNeighbourMoves (b : Build) : List (GearSlot × StatCombo) :=
  GearSlot.all.flatMap fun slot =>
    (allCombos.filter (· ≠ b.gear slot)).map fun c => (slot, c)
def defaultCombo : StatCombo := default
def setBuildSlot (b : Build) (slot : GearSlot) (combo : StatCombo) : Build :=
  { b with gear := fun s => if s == slot then combo else b.gear s }

structure TabuState where
  current   : Build
  currentPen : Nat
  best      : Build
  bestPen   : Nat
  tabuList  : List (GearSlot × StatCombo)  -- recently changed
  tabuTenure : Nat                          -- how long moves stay tabu

def tabuStep (state : TabuState) (targets : StatType → Nat)
    : TabuState :=
  let candidates := allNeighbourMoves state.current
    |>.filter fun (slot, combo) =>
      -- Allow if not tabu, OR if it produces a new global best
      ¬ state.tabuList.contains (slot, combo)
  let (bestSlot, bestCombo, bestPen) := candidates.foldl
    (init := ((GearSlot.headgear, defaultCombo, 1000000000) : GearSlot × StatCombo × Nat))
    -- DEVIATION: book's sentinel is `Nat.max` (a function; type error);
    -- the tuple also needs an ascription for `.headgear` to elaborate.
    fun (bs, bc, bp) (slot, combo) =>
      let build := setBuildSlot state.current slot combo
      let pen := totalPenalty build targets wMiss wOver
      if pen < bp then (slot, combo, pen) else (bs, bc, bp)
  let newBuild := setBuildSlot state.current bestSlot bestCombo
  let newTabu := ((bestSlot, state.current.gear bestSlot) :: state.tabuList)
    |>.take state.tabuTenure  -- keep only recent entries
  { current := newBuild
    currentPen := bestPen
    best := if bestPen < state.bestPen then newBuild else state.best
    bestPen := min bestPen state.bestPen
    tabuList := newTabu
    tabuTenure := state.tabuTenure }

/- ============================================================
   §Ch.8 — Genetic algorithm (tex 1955–1984).
   Compiles once `randomBool` and `tournamentSelect` are stubbed
   (never defined in the book).
   ============================================================ -/

-- DEVIATION (stubs)
def randomBool (rng : StdGen) : Bool × StdGen :=
  let (n, rng') := randNat rng 0 1
  (n == 1, rng')
def tournamentSelect (pop : Array Build) (fits : Array Nat)
    (_k : Nat) (rng : StdGen) : Build × StdGen :=
  let (n, rng') := randNat rng 0 (pop.size - 1)
  (pop[n % pop.size]!, rng')

/-- Uniform crossover: for each slot, pick from parent A or B. -/
def crossover (a b : Build) (rng : StdGen) : Build × StdGen :=
  GearSlot.all.foldl (init := (a, rng)) fun (child, rng) slot =>
    let (bit, rng) := randomBool rng
    let combo := if bit then a.gear slot else b.gear slot
    ({ child with gear := fun s => if s == slot then combo else child.gear s }, rng)

/-- Mutate: change one random slot to a random combo. -/
def mutate (b : Build) (rng : StdGen) (mutRate : Float := 0.1)
    : Build × StdGen :=
  let (r, rng) := randomFloat rng
  if r > mutRate then (b, rng)
  else
    let (slot, rng) := randomSlot rng
    let (combo, rng) := randomCombo rng allCombos
    ({ b with gear := fun s => if s == slot then combo else b.gear s }, rng)

/-- One generation of the GA. -/
def gaGeneration (pop : Array Build) (targets : StatType → Nat)
    (rng : StdGen) : Array Build × StdGen :=
  let fitnesses := pop.map (fun b => totalPenalty b targets wMiss wOver)
  (Array.range pop.size).foldl (init := (#[], rng)) fun (newPop, rng) _ =>
    -- Tournament selection (pick 3, keep best)
    let (parent1, rng) := tournamentSelect pop fitnesses 3 rng
    let (parent2, rng) := tournamentSelect pop fitnesses 3 rng
    let (child, rng) := crossover parent1 parent2 rng
    let (child, rng) := mutate child rng
    (newPop.push child, rng)

/- ============================================================
   §Ch.9 (Pareto) — Dominance (tex 2059–2093).
   `dominates`, `dominates_irrefl` compile VERBATIM.
   *** GENUINELY PROVED (no sorry) ***: `dominates_irrefl`,
   `dominates_trans`, and the `Decidable (dominates a b)` instance.
   The book's printed `dominates_trans` FAILED (`Nat.le_trans …|>.symm`
   — `≤` has no `.symm` — followed by an unreachable tactic); the
   corrected proof below closes both goals. The book's printed
   `Decidable` instance left FOUR `sorry`s; the version below discharges
   all of them via a boolean test and `decidable_of_iff`, so dominance
   is now genuinely decidable AND computes (see `#eval`s).
   `paretoFrontier` FAILS AS PRINTED: it uses `dominates` inside
   `List.any` (needs Bool) BEFORE the instance is declared, so the
   instance must precede it.
   ============================================================ -/

/-- Every `StatType` is in the enumeration `StatType.all`. -/
theorem StatType.mem_all (s : StatType) : s ∈ StatType.all := by
  cases s <;> decide

/-- Build a dominates build b. -/
def dominates (a b : Build) : Prop :=
  (∀ s : StatType, statTotal a s ≥ statTotal b s) ∧
  (∃ s : StatType, statTotal a s > statTotal b s)

/-- Dominance is irreflexive. -/
theorem dominates_irrefl (a : Build) : ¬ dominates a a := by
  intro ⟨_, ⟨s, hs⟩⟩
  exact Nat.lt_irrefl _ hs

/-- Dominance is transitive. -/
theorem dominates_trans {a b c : Build}
    (hab : dominates a b) (hbc : dominates b c) : dominates a c := by
  constructor
  · intro s
    exact Nat.le_trans (hbc.1 s) (hab.1 s)
    -- DEVIATION: book writes `exact Nat.le_trans (hbc.1 s) (hab.1 s) |>.symm`
    -- (`.symm` does not exist for `≤`) followed by an unreachable `sorry`.
    -- Without the spurious `.symm` the term already closes the goal.
  · obtain ⟨s, hs⟩ := hab.2
    exact ⟨s, Nat.lt_of_le_of_lt (hbc.1 s) hs⟩
    -- DEVIATION: book writes `Nat.lt_of_lt_of_le hs (hbc.1 s) |>.symm`
    -- — no `.symm` on `<`, and the composition direction is wrong.
    -- Correct: carry the strictness through the SECOND relation with
    -- `Nat.lt_of_le_of_lt (c ≤ b) (b < a)`.

-- The Decidable instance must precede `paretoFrontier` (the book prints
-- it after, so `paretoFrontier` fails to elaborate).
/-- Boolean dominance test, used to derive `Decidable`. -/
def dominatesBool (a b : Build) : Bool :=
  (StatType.all.all fun s => statTotal b s ≤ statTotal a s) &&
  (StatType.all.any fun s => statTotal b s < statTotal a s)

/-- Decidable dominance for computation — GENUINELY PROVED (no sorry). -/
instance : Decidable (dominates a b) :=
  decidable_of_iff (dominatesBool a b = true) (by
    unfold dominatesBool dominates
    rw [Bool.and_eq_true, List.all_eq_true, List.any_eq_true]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨fun s => ?_, ?_⟩
      · have := h1 s (StatType.mem_all s); simpa using this
      · obtain ⟨s, _, hs⟩ := h2; exact ⟨s, by simpa using hs⟩
    · rintro ⟨h1, s, hs⟩
      exact ⟨fun s _ => by simpa using h1 s,
             ⟨s, StatType.mem_all s, by simpa using hs⟩⟩)

/-- The Pareto frontier: all non-dominated builds. -/
def paretoFrontier (builds : List Build) : List Build :=
  builds.filter fun b =>
    ¬ builds.any fun a => dominates a b

/- ============================================================
   §Ch.9 (Pareto) — ε-constraint sweep (tex 2160–2178).
   Needs `GearProblem` and `solve` (defined only two chapters
   LATER, and even then over Finset domains). With stubs the
   listing compiles.
   ============================================================ -/

inductive SolverResult where                     -- (tex 2313–2315, Ch.11)
  | optimal    : Build → Nat → SolverResult   -- build + penalty
  | infeasible : SolverResult

-- DEVIATION (stub): the real `solve` (tex 2317) needs Finset; see the
-- Mathlib file. A stub is used so the Ch.9 sweep listings elaborate.
def solve (_ : GearProblem) : SolverResult := .infeasible

/-- Trace the Pareto frontier by sweeping an epsilon constraint. -/
def epsilonConstraintSweep
    (problem : GearProblem)
    (primaryStat : StatType)      -- optimise this
    (constrainedStat : StatType)  -- constrain this
    (minVal maxVal step : Nat)    -- sweep range
    : List (Nat × Nat × Build) :=  -- (primary, constrained, build)
  (List.range ((maxVal - minVal) / step + 1)).filterMap fun i =>
    let threshold := minVal + i * step
    let constrained := { problem with
      targets := fun s =>
        if s == constrainedStat then threshold
        else problem.targets s }
    match solve constrained with
    | .optimal build pen => some (statTotal build primaryStat,
                                  statTotal build constrainedStat, build)
    | .infeasible => none

/- ============================================================
   §Ch.10 — Infusion DP (tex 2225–2243).
   FAILS AS PRINTED — this is the most broken listing in the book:
   1. `Array.mkArray` — removed in v4.31 (→ `Array.replicate`).
   2. `stats.foldl (init := dp) fun dp i stat => ...` — foldl's
      function takes TWO arguments (acc, element); three are given:
      "function expected" / type mismatch.
   3. The fold body returns one ROW (`Array (Nat × Array Nat)`),
      but the accumulator is the whole table — type mismatch —
      and consequently `dp[i]!` inside the body indexes the OLD
      table while `i` is not even in scope.
   4. `.mapIdx fun r _ => ... r.val ...` — in v4.31 `Array.mapIdx`
      passes a `Nat` index, so `r.val` fails ("Unknown field val").
   5. `(Nat.max, #[])` sentinel — `Nat.max` is a function.
   6. `stats.indexOf stat` — no `Array.indexOf` in v4.31
      (→ `Array.idxOf`).
   7. Semantic bug even after repairs: `allocRest.push ni` appends
      stat i's allocation to the END of the sub-allocation, but the
      final extraction `alloc[stats.indexOf stat]!` reads it at
      position i — the allocation array is reversed.
   Below: a minimally-repaired version (DEVIATION) that fixes 1–7,
   plus an #eval sanity check of DP optimality on a small instance.
   ============================================================ -/

def infusionDP (gearStats : StatType → Nat)
    (targets : StatType → Nat) (budget : Nat := 18)
    : StatType → Nat :=
  let stats := StatType.all.toArray
  -- dp[r] = (minPenalty, allocation for stats processed so far),
  -- indexed by remaining budget AFTER processing those stats.
  let init : Array (Nat × Array Nat) := Array.replicate (budget + 1) (0, #[])
  let dp := stats.foldl (init := init) fun dp stat =>
    (Array.range (budget + 1)).map fun r =>
      let best := (List.range (r + 1)).foldl
        (init := (1000000000, #[])) fun acc ni =>
        let penHere := penalty (targets stat) (gearStats stat + 5 * ni) wMiss wOver
        let (penRest, allocRest) := dp[r - ni]!
        let total := penHere + penRest
        if total < acc.1 then (total, allocRest.push ni) else acc
      best
  -- Extract the allocation from dp[budget]
  let (_, alloc) := dp[budget]!
  fun stat => alloc[stats.idxOf stat]!

-- Sanity check of the REPAIRED DP: two-stat toy instance.
-- Gear gives Power 0/Precision 0, targets Power 40, Precision 50,
-- budget 18 (90 points): optimum fills Power with 8 (40) and
-- Precision with 10 (50): penalty 0.  The DP finds it.
def toyGear : StatType → Nat := fun _ => 0
def toyTargets : StatType → Nat
  | .power => 40 | .precision => 50 | _ => 0
def toyAlloc : StatType → Nat := infusionDP toyGear toyTargets 18
#eval (StatType.all.map toyAlloc) -- allocation: [8, 10, 0, 0, 0, 0, 0, 0, 0]
#eval (StatType.all.map fun s =>
  penalty (toyTargets s) (toyGear s + 5 * toyAlloc s)
    wMiss wOver).sum   -- = 0 (all targets met exactly; 8+10=18 ✓)

/- ============================================================
   §Ch.11 — Solver loop (tex 2313–2360): needs Finset ⇒ verified
   in the Mathlib file (where its own errors are recorded:
   `simulatedAnnealing` called with the wrong arity, a `Build × Nat`
   used as a `Build`, `Finset.fold` misused, a missing `some`, and
   the `| none => .infeasible` branch is DEAD CODE — `branchAndBound`
   never returns `none`, so the solver can never report
   infeasibility from B&B).
   ============================================================ -/

/- ============================================================
   §Ch.12 — Correctness theorem statement (tex 2377–2387).
   The book displays the statement without proof; `Build.feasible`
   is never defined (Build has no such field/def) — stubbed.
   ============================================================ -/

-- DEVIATION (stub): `Build.feasible` never defined in the book.
-- MODELLING RECONCILIATION (REVIEW.md #1/#3): the solver's LinearGeq
-- propagation treats the stat targets as HARD FLOORS, so `feasible`
-- must include the floor constraint `statTotal b s ≥ targets s` for
-- the soundness theorem to be TRUE. With this definition the solver
-- solves "minimise penalty (overshoot) over builds meeting every
-- floor, else report infeasible" — the problem the CODE actually
-- decides. (The pure soft-penalty problem of Ch.1 is DIFFERENT and
-- LinearGeq is NOT sound for it: it can prune the soft optimum.)
def Build.feasible (b : Build) (p : GearProblem) : Prop :=
  (∀ slot, b.gear slot ∈ p.initialDomains slot) ∧
  ((StatType.all.map b.infusions).sum = 18) ∧
  (∀ s, statTotal b s ≥ p.targets s)   -- HARD stat floors

theorem solver_sound (problem : GearProblem) :
    match solve problem with
    | .optimal build pen =>
        build.feasible problem ∧
        pen = totalPenalty build problem.targets wMiss wOver ∧
        ∀ b, b.feasible problem →
          totalPenalty b problem.targets wMiss wOver ≥ pen
    | .infeasible =>
        ∀ b : Build, ¬ b.feasible problem := by
  sorry
-- HONEST SPECIFICATION: the book prints this statement without proof
-- (proof left as an extended exercise). With the hard-floor `feasible`
-- above the statement is TRUE-in-principle and matches what `solve`
-- computes; the full proof needs the component lemmas
-- (linearGeq_sound, propagation_preserves_feasible, lp_bound_valid,
-- bb_step_preserves) and is a substantial formalisation task.

/- ============================================================
   §Ch.12 — B&B invariant structure (tex 2520–2535).
   FAILS AS PRINTED: `BBState`, `BBNode` never defined;
   `totalPenalty b ≥ state.incumbent.penalty` compares a PARTIALLY
   APPLIED function (totalPenalty takes 4 arguments) with a Nat —
   type error. Minimal stubs + fix below.
   ============================================================ -/

-- DEVIATION (stubs): `BBNode`/`BBState` never defined in the book.
structure BBNode where
  domains : GearSlot → List StatCombo
  lpBound : Nat
def Build.inSubtree (b : Build) (n : BBNode) : Prop :=
  ∀ s, b.gear s ∈ n.domains s
structure Incumbent where
  build   : Build
  penalty : Nat
def Incumbent.feasible (i : Incumbent) (p : GearProblem) : Prop :=
  i.build.feasible p
structure BBState where
  problem   : GearProblem
  incumbent : Incumbent
  pruned    : List BBNode
  queue     : List BBNode
def bbStep (s : BBState) : BBState := s   -- DEVIATION (stub)

/-- The B&B invariant: incumbent is feasible and dominates all pruned nodes. -/
structure BBInvariant (state : BBState) where
  incumbent_feasible : state.incumbent.feasible state.problem
  pruned_bounded : ∀ node ∈ state.pruned,
    node.lpBound ≥ state.incumbent.penalty
  partition : ∀ b : Build, b.feasible state.problem →
    (totalPenalty b state.problem.targets wMiss wOver ≥ state.incumbent.penalty) ∨
    -- DEVIATION: book writes `totalPenalty b ≥ ...` — missing the
    -- targets/weight arguments (type error: function ≥ Nat).
    (∃ node ∈ state.queue, b.inSubtree node)

/-- Each step of B&B preserves the invariant. -/
theorem bb_step_preserves (state : BBState)
    (h_inv : BBInvariant state)
    (state' : BBState)
    (h_step : state' = bbStep state) :
    BBInvariant state' := by
  sorry -- BOOK'S OWN SORRY ("case split on branch/prune/evaluate")

/- ============================================================
   §Ch.12 — Infusion DP optimality (tex 2568–2579).
   `totalInfusionPenalty` never defined — stubbed. Book's sorry.
   ============================================================ -/

-- DEVIATION (stub): never defined in the book.
def totalInfusionPenalty (gearStats targets : StatType → Nat)
    (alloc : StatType → Nat) : Nat :=
  (StatType.all.map fun s =>
    penalty (targets s) (gearStats s + 5 * alloc s) wMiss wOver).sum

/-- The DP allocation minimises penalty among all valid allocations. -/
theorem infusion_dp_optimal
    (gearStats : StatType → Nat) (targets : StatType → Nat)
    (budget : Nat) :
    let dpAlloc := infusionDP gearStats targets budget
    ∀ alloc : StatType → Nat,
      (StatType.all.map alloc).sum = budget →
      totalInfusionPenalty gearStats targets dpAlloc ≤
      totalInfusionPenalty gearStats targets alloc := by
  -- By induction on StatType.all.length (= 9)
  -- using the recurrence relation of the DP table
  sorry -- BOOK'S OWN SORRY

/- ============================================================
   §Ch.13 — BitVec domains (tex 2654–2661).
   FAILS AS PRINTED (two errors):
   1. `d.popcount` — no `BitVec.popcount` in v4.31; the operation
      is `BitVec.cpop` and returns `BitVec 40`, not `Nat`
      (need `.toNat`).
   2. `d &&& ~~~(1 <<< i.val)` — `1 <<< i.val` elaborates at `Nat`,
      and `~~~` then fails: "failed to synthesize Complement Nat".
      The literal must be ascribed to `BitVec 40`.
   ============================================================ -/

/-- A domain is a 40-bit vector: bit i = 1 iff combo i is still possible. -/
abbrev Domain := BitVec 40

def Domain.intersect (a b : Domain) : Domain := a &&& b
def Domain.isEmpty (d : Domain) : Bool := d == 0
def Domain.card (d : Domain) : Nat := d.cpop.toNat
-- DEVIATION: book has `d.popcount` (no such constant; `cpop` returns a
-- BitVec so `.toNat` is also required).
def Domain.remove (d : Domain) (i : Fin 40) : Domain :=
  d &&& ~~~((1 : BitVec 40) <<< i.val)
-- DEVIATION: book's `~~~(1 <<< i.val)` fails (Complement Nat).

#eval Domain.card (Domain.remove (BitVec.allOnes 40) ⟨7, by omega⟩)  -- 39 ✓

/- ============================================================
   §Ch.13 — Precomputed tables (tex 2693–2705): compiles given
   the `allCombos`/`GearSlot.all`/`StatType.all` stubs.
   ============================================================ -/

/-- Precompute contribution of each combo to each stat on each slot.
    Access: contribTable[slot][combo][stat] -/
def buildContribTable : Array (Array (Array Nat)) :=
  GearSlot.all.toArray.map fun slot =>
    allCombos.toArray.map fun combo =>
      StatType.all.toArray.map fun stat =>
        contribution slot combo stat

/-- Precompute max contribution per stat per domain.
    Avoids recomputing during propagation. -/
structure DomainStats where
  maxPerStat  : Array Nat   -- maxPerStat[stat] = max contribution in domain
  minPerStat  : Array Nat   -- minPerStat[stat] = min contribution in domain
  sumMaxPower : Nat         -- cached sum for quick feasibility check

/- ============================================================
   §Ch.13 — Incremental propagation (tex 2717–2740).
   FAILS AS PRINTED:
   1. `state.dirty.toList.enum` — `List.enum` removed in v4.31
      (now `zipIdx`, which also swaps the pair order!).
   2. `linearGeqFilter`, `GearSlot.toIdx` never defined.
   3. `partial` recursion is fine, but termination is NOT
      structural — the book does not remark on this.
   ============================================================ -/

-- DEVIATION (stubs)
def GearSlot.toIdx : GearSlot → Nat
  | .headgear => 0 | .shoulders => 1 | .coat => 2 | .gloves => 3
  | .leggings => 4 | .boots => 5 | .mainhand => 6 | .offhand => 7
  | .amulet => 8 | .ring1 => 9 | .ring2 => 10 | .accessory1 => 11
  | .accessory2 => 12 | .backPiece => 13
def linearGeqFilter (ds : Array Domain) (slot : GearSlot)
    (_ : StatType → Nat) : Domain := ds[slot.toIdx]!  -- DEVIATION (stub)

structure PropState where
  domains    : Array Domain           -- one per slot (14 entries)
  dirty      : Array Bool             -- which slots changed?
  domStats   : Array DomainStats      -- cached per-slot stats
  feasible   : Bool                   -- still feasible?

/-- Propagate incrementally: only process dirty slots. -/
partial def propagateIncremental (state : PropState)
    (targets : StatType → Nat) : PropState :=
  let dirtySlots := state.dirty.toList.zipIdx.filter (·.1) |>.map (·.2)
  -- DEVIATION: book has `.enum.filter (·.2) |>.map (·.1)`; `List.enum`
  -- was removed in v4.31 and `zipIdx` yields (elem, idx), not (idx, elem).
  if dirtySlots.isEmpty then state  -- fixpoint reached
  else
    let state' := dirtySlots.foldl (init := { state with dirty := state.dirty.map (fun _ => false) })
      fun st slotIdx =>
        -- Re-run LinearGeq for all slots that might be affected
        GearSlot.all.foldl (init := st) fun st2 slot =>
          let newDomain := linearGeqFilter st2.domains slot targets
          if newDomain != st2.domains[slot.toIdx]! then
            { st2 with
              domains := st2.domains.set! slot.toIdx newDomain
              dirty := st2.dirty.set! slot.toIdx true }
          else st2
    propagateIncremental state' targets  -- recurse until clean

/- RECONCILED: the book now consistently uses 14 slots (GearSlot has 14
   constructors), so PropState says "14 entries" and UndoEntry uses
   `Fin 14`. The earlier 14-vs-16 drift is resolved. -/

/- ============================================================
   §Ch.13 — Undo stack (tex 2755–2768): compiles VERBATIM.
   ============================================================ -/

structure UndoEntry where
  slot     : Fin 14
  oldDomain : Domain

/-- Save the current domain before a branch. -/
def saveState (domains : Array Domain) (slot : Fin 14)
    : UndoEntry :=
  ⟨slot, domains[slot]!⟩

/-- Restore domain after backtracking. -/
def restoreState (domains : Array Domain) (entry : UndoEntry)
    : Array Domain :=
  domains.set! entry.slot entry.oldDomain

/- ============================================================
   §Ch.13 — Compiler hints (tex 2779–2793).
   FAILS AS PRINTED:
   1. `contribTable` (used by `contribution'`) is never defined —
      the earlier listing defines `buildContribTable`. Name drift.
   2. `@[specialize] def propagateWith [BEq D] [Domain D]` —
      `Domain` is an `abbrev` for `BitVec 40`, NOT a typeclass:
      "invalid binder annotation, type is not a class".
   3. Its body is the book's own `sorry` — but a `def` whose body
      is `sorry` also needs the signature repaired first.
   ============================================================ -/

-- DEVIATION (stub): name drift — book defines `buildContribTable` but
-- reads `contribTable`.
def contribTable : Array (Array (Array Nat)) := buildContribTable

-- Force inlining of hot inner loops
@[inline] def contribution' (slot : GearSlot) (comboIdx : Fin 40)
    (statIdx : Fin 9) : Nat :=
  contribTable[slot.toIdx]![comboIdx]![statIdx]!

-- DEVIATION: book writes `[BEq D] [Domain D]` — `Domain` is an abbrev,
-- not a class ("invalid binder annotation … not a class"). A Propagator
-- type is also never defined. Minimal repair: a real class + stub.
class DomainLike (D : Type) where
  isEmpty : D → Bool
structure Propagator (D : Type) where
  fire : Array D → Array D

@[specialize] def propagateWith [BEq D] [DomainLike D]
    (domains : Array D) (props : Array (Propagator D)) : Array D :=
  sorry -- BOOK'S OWN SORRY

-- Use unboxed representations where possible
structure PackedBuild where
  slots     : BitVec 240  -- 16 slots × 6 bits each (enough for 40 combos)
  runeIdx   : UInt8
  infusions : BitVec 72   -- 9 stats × 8 bits each (max 18 per stat)

/- ============================================================
   §Ch.14 — Food/utility (tex 2851–2867): compiles VERBATIM.
   ============================================================ -/

structure FoodItem where
  name  : String
  stats : StatType → Nat  -- flat bonuses (e.g., +100 Power, +70 Ferocity)

structure UtilityItem where
  name  : String
  stats : StatType → Nat  -- flat bonuses (e.g., +100 Precision)

/-- Extended build includes food and utility. -/
structure ExtBuild extends Build where
  food    : FoodItem
  utility : UtilityItem

/-- Extended stat total includes food/utility contributions. -/
def extStatTotal (b : ExtBuild) (s : StatType) : Nat :=
  statTotal b.toBuild s + b.food.stats s + b.utility.stats s

/- ============================================================
   §Ch.14 — Trait conversions (tex 2899–2913): COMPILES VERBATIM
   but has a SEMANTIC BUG: the fold's `then` branch DISCARDS the
   accumulator, so with several conversions targeting the same
   stat only the LAST one counts, and even a single conversion is
   only correct because acc starts at 0. Should be
   `acc + conv.percentage * ...`. Demonstrated by #eval below.
   ============================================================ -/

structure TraitConversion where
  sourceStat : StatType
  targetStat : StatType
  percentage : Float   -- e.g., 0.07 for 7%

/-- Stat total with trait conversions applied. -/
def traitStatTotal (b : Build) (conversions : List TraitConversion)
    (s : StatType) : Float :=
  let base := (statTotal b s).toFloat
  let bonus := conversions.foldl (init := 0.0) fun acc conv =>
    if conv.targetStat == s then
      conv.percentage * (statTotal b conv.sourceStat).toFloat
    else acc
  base + bonus

-- Demonstration of the bug: two 10% conversions into Power should add
-- both bonuses; the printed code keeps only the second.
def twoConvs : List TraitConversion :=
  [⟨.toughness, .power, 0.1⟩, ⟨.vitality, .power, 0.1⟩]
def bugBuild : Build :=
  { gear := fun _ => default, rune := ⟨""⟩,
    infusions := fun s => if s == StatType.toughness then 10 else
                          if s == StatType.vitality then 8 else 0 }
-- toughness total = 50, vitality total = 40; correct bonus = 5 + 4 = 9,
-- so traitStatTotal should be 9.0; the printed code yields 4.0:
#eval traitStatTotal bugBuild twoConvs .power   -- 4.0, not 9.0 → bug confirmed

/- ============================================================
   §Ch.14 — What-if mode (tex 2959–2973) uses Finset ⇒ Mathlib
   file (`berserkers` also never defined).
   ============================================================ -/

/- ============================================================
   §Ch.14 — Pareto frontier mode (tex 3002–3024).
   FAILS AS PRINTED:
   1. `(w * 100).toNat` — `Float.toNat` does not exist in v4.31
      ("Unknown constant `Float.toNat`"). Repaired via
      `.toUInt64.toNat`.
   2. `{ problem with wMissPerStat := ... }` — `GearProblem` was
      never given a `wMissPerStat` field anywhere in the book;
      every other listing uses global scalars `wMiss`/`wOver`.
      Notation drift; the stub GearProblem above adds the field so
      this elaborates.
   `filterDominated` compiles verbatim.
   ============================================================ -/

/-- Generate the Pareto frontier by sweeping scalarisation weights. -/
def paretoFrontierMode (problem : GearProblem)
    (statA statB : StatType) (nPoints : Nat := 20)
    : List (Build × Nat × Nat) :=
  (List.range (nPoints + 1)).filterMap fun i =>
    let w := (i.toFloat) / nPoints.toFloat  -- weight for statA miss
    let weightedProblem := { problem with
      wMissPerStat := fun s =>
        if s == statA then (w * 100).toUInt64.toNat
        else if s == statB then ((1.0 - w) * 100).toUInt64.toNat
        else 50 }  -- default weight for other stats
    -- DEVIATION: book writes `(w * 100).toNat` — no `Float.toNat`.
    match solve weightedProblem with
    | .optimal build pen =>
      some (build, statTotal build statA, statTotal build statB)
    | .infeasible => none

/-- Filter to non-dominated solutions. -/
def filterDominated (results : List (Build × Nat × Nat))
    : List (Build × Nat × Nat) :=
  results.filter fun (_, a1, b1) =>
    ¬ results.any fun (_, a2, b2) =>
      (a2 ≥ a1 ∧ b2 ≥ b1) ∧ (a2 > a1 ∨ b2 > b1)

/- ============================================================
   MACHINE CHECK of the Chapter 6 worked example (tex 1362–1413).
   The book claims: with targets Power ≥ 300 and NO infusions,
   LinearGeq removes exactly Celestial from each of the three
   slots, leaving {Berserker's, Marauder} everywhere.
   FALSE: without infusions the maximum reachable Power is
   141+94+47 = 282 < 300, so LinearGeq removes EVERY combo from
   EVERY slot (instant infeasibility); and with the 90-point
   infusion budget the propagator (as defined at tex 794–820)
   removes ONLY coat-Celestial (67+141+90 = 298 < 300; both other
   Celestial placements survive: 322, 347 ≥ 300).
   ============================================================ -/

def ch6Combos : List StatCombo :=
  [⟨"Berserker's", .triple, [.power], [.precision, .ferocity]⟩,
   ⟨"Marauder", .quad, [.power, .precision], [.vitality, .ferocity]⟩,
   ⟨"Celestial", .celestial, [], []⟩]
def ch6Slots : List GearSlot := [.coat, .leggings, .boots]

def ch6MaxContrib (slot : GearSlot) : Nat :=
  (ch6Combos.map fun c => contribution slot c .power).foldl max 0

/-- LinearGeq survivor set for a slot, following tex 794–820, with
    a configurable infusion budget. -/
def ch6Survivors (slot : GearSlot) (infusionBudget : Nat) : List String :=
  ch6Combos.filter (fun combo =>
    let myContrib := contribution slot combo .power
    let othersMax := ((ch6Slots.filter (· ≠ slot)).map ch6MaxContrib).foldl (·+·) 0
    myContrib + othersMax + infusionBudget ≥ 300) |>.map (·.name)

#eval ch6Slots.map (fun s => (repr s, ch6Survivors s 0))
-- ⇒ ALL empty: [[], [], []] — not {Berserker's, Marauder} as the book claims.
#eval ch6Slots.map (fun s => (repr s, ch6Survivors s 90))
-- ⇒ coat loses only Celestial; leggings and boots keep all three —
--   also not what the book claims.

/- ============================================================
   MACHINE CHECK of the Chapter 4 duality direction (tex 1071–1084).
   The book pairs  min cᵀx  s.t. Ax ≤ b, x ≥ 0   with
                   max bᵀy  s.t. Aᵀy ≥ c, y ≥ 0
   and claims weak duality cᵀx ≥ bᵀy, while its own proof derives
   cᵀx ≤ bᵀy. Counterexample to the claimed direction (1×1):
   A = (1), b = (1), c = (1): primal x = 0 feasible (0 ≤ 1),
   cᵀx = 0; dual y = 2 feasible (1·2 ≥ 1), bᵀy = 2. 0 ≥ 2 is false.
   ============================================================ -/
example : ¬ ((0 : Int) ≥ 2) := by omega
-- (Primal feasibility: 1*0 ≤ 1 ∧ 0 ≥ 0; dual feasibility: 1*2 ≥ 1 ∧ 2 ≥ 0.)
example : (1 : Int) * 0 ≤ 1 ∧ (0 : Int) ≥ 0 := by omega
example : (1 : Int) * 2 ≥ 1 ∧ (2 : Int) ≥ 0 := by omega

/- ------------------------------------------------------------
   The CORRECTED (standard) lower-bounding dual pairing that the
   book now uses (tex Ch.4): primal  min cᵀx  s.t. Ax ≥ b, x ≥ 0;
   dual  max bᵀy  s.t. Aᵀy ≤ c, y ≥ 0; weak duality  cᵀx ≥ bᵀy.
   1×1 sanity check A=(1),b=(1),c=(1): primal feasible ⇒ x ≥ 1;
   dual feasible ⇒ 0 ≤ y ≤ 1; then cᵀx = x ≥ 1 ≥ y = bᵀy. ------- -/
example (x y : Int) (hpx : (1:Int) * x ≥ 1) (hxnn : x ≥ 0)
    (hdy : (1:Int) * y ≤ 1) (hynn : y ≥ 0) :
    (1:Int) * x ≥ 1 * y := by omega

/- ============================================================
   §Appendix A — "A Lean 4 Primer": every construct/tactic the
   appendix documents, machine-checked here (core Lean).
   ============================================================ -/
namespace Primer

inductive Colour where
  | red | green | blue
  deriving DecidableEq, Repr

def Colour.code : Colour → Nat
  | .red => 0 | .green => 1 | .blue => 2

-- theorem / example, intro / exact
example (p q : Prop) (hp : p) (h : p → q) : q := h hp
example (p q : Prop) : p → (p → q) → q := by
  intro hp h
  exact h hp

-- rfl
example : 2 + 3 = 5 := rfl

-- constructor (∧)
example (p q : Prop) (hp : p) (hq : q) : p ∧ q := by
  constructor
  · exact hp
  · exact hq

-- obtain (∃/∧) and its Exists.elim desugaring
example (P : Nat → Prop) (h : ∃ n, P n) : ∃ m, P m := by
  obtain ⟨n, hn⟩ := h
  exact ⟨n, hn⟩
example (P : Nat → Prop) (h : ∃ n, P n) : ∃ m, P m :=
  Exists.elim h (fun n hn => ⟨n, hn⟩)

-- unfold
def sq (n : Nat) : Nat := n * n
example : sq 3 = 9 := by unfold sq; rfl

-- simp
example (n : Nat) : n + 0 = n := by simp

-- omega
example (a b : Nat) (h : a + 1 < b) : a < b := by omega

-- split (on an if/match in the goal)
def clip (n : Nat) : Nat := if n < 10 then n else 10
example (n : Nat) : clip n ≤ 10 := by
  unfold clip
  split
  · omega
  · omega

-- induction ... with, and its recursor desugaring
theorem zero_add_nat (n : Nat) : 0 + n = n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Nat.add_succ, ih]

theorem zero_add_nat' (n : Nat) : 0 + n = n :=
  Nat.rec (motive := fun n => 0 + n = n)
    rfl
    (fun n ih => by show 0 + (n + 1) = n + 1; rw [Nat.add_succ, ih])
    n

-- cases (on a value)
def isRed : Colour → Bool
  | .red => true | _ => false
example (c : Colour) : isRed c = true ∨ isRed c = false := by
  cases c with
  | red => left; rfl
  | green => right; rfl
  | blue => right; rfl

-- sorry: an admitted, UNPROVEN goal (leaves a warning; NOT a real proof)
theorem unproven (n : Nat) : n + 0 = n := by sorry -- BOOK'S OWN (primer) SORRY

end Primer

end VO
