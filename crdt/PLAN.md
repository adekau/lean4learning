# PLAN — "From Propagators to Replicas" (working title)
### CRDTs in Lean 4 — sequel to *From Zero to Propagators* (lean4learning series)

This file is the complete brief for writing the book. It assumes the reader of
this plan has access to the repo but no other context. The predecessor book is
`/home/adekau/lean4learning/order-lattices/from-zero-to-propagators.tex` with
companion `/home/adekau/lean4learning/order-lattices/OrderAndLattices.lean`.
Read both before writing a word — the sequel must feel continuous with them.

---

## 1. One-page pitch and thesis

**Thesis.** A state-based CRDT is a propagator cell with a network attached.
The predecessor book ended with cells that accumulate partial information via
joins inside one process: state lives in a bounded join-semilattice, updates
are monotone, and writing is merging (`c ← c ⊔ v`). This book takes exactly
that discipline and stretches it across an unreliable network. Each replica is
a cell; `merge` is the join; an update is a monotone step upward; and
**strong eventual consistency is nothing but the algebra of join**: because
`⊔` is commutative, associative, and idempotent, replicas that have received
the same set of updates — in any order, any number of times — compute the same
fold and therefore hold equal state. The network's three sins (reordering,
duplication, and redelivery) are absorbed by commutativity+associativity,
idempotence, and idempotence again. Nothing else is needed, and (the book
proves by refutation) nothing less suffices.

**Arc.** Part I motivates replication and restates the propagator vocabulary
as a *merge discipline*. Part II builds the classic zoo — G-Counter,
PN-Counter, G-Set, 2P-Set, LWW-Register, LWW-Element-Set, OR-Set — each as a
Lean structure with a verified `BoundedJoinSemilattice` instance, each
motivated by a *refutation* of the previous design's naive extension. Part III
proves the main theorem: strong eventual consistency for any state-based CRDT,
via a join-fold over the multiset of delivered updates (this is where the
reader meets **quotient types**, deliberately). Part IV covers delivery
semantics, version vectors, op-based CRDTs, a capstone replicated store with
an IO simulation harness (the sequel to `runToFixpoint`), and an honest
closing chapter on what CRDTs cannot do.

**Why this book is worth writing.** Every CRDT tutorial hand-waves
convergence ("it's a semilattice, so it works"). This book has already built
the semilattice machinery from axioms in the predecessor; it is uniquely
positioned to make "so it works" a theorem with a name, a proof, zero
dependencies, and a `#eval`-able demonstration of duplicated, reordered
delivery converging anyway.

**Length target.** ~120–150 pages typeset, 13 chapters in 4 parts, 2 appendices;
companion `Crdt.lean` ≈ 2,300 lines, zero sorries, stdlib only.

---

## 2. Prerequisites and calibration

**Assumed (from the predecessor book, do not re-teach, do recap):**
partial orders, bounded join-semilattices, lattices, monotone maps,
Knaster–Tarski, hand-rolled typeclasses (`PartialOrder`,
`BoundedJoinSemilattice` with fields `sup/bot/le_sup_left/le_sup_right/
sup_le/bot_le`), notation `⊑/≤ ⊔ ⊓ ⊥ ⊤`, structural induction, custom
inductive predicates, strong induction, classical reasoning where needed,
`decide` / `omega` / `simp_all`, monadic IO Lean, the propagator scheduler
pattern (`Cell`, `PropStep`, `runToFixpoint`).

**Reader's known gaps — the book deliberately exercises these:**
- **Quotient types** (never used): the star of Chapter 8. Finite multisets of
  delivered updates are `Quotient` of `List` by permutation; the join-fold is
  lifted with `Quotient.lift` + a permutation-invariance proof. Introduce
  `Setoid`, `Quotient.mk`, `Quotient.lift`, `Quotient.sound`, `Quotient.ind`
  from scratch, slowly, with a toy example (integers as ℕ×ℕ pairs) before the
  real one.
- **Well-founded recursion** (recently learned, needs reps): the anti-entropy
  termination argument in Chapter 9 — gossip rounds terminate because a
  natural-number measure ("total updates not yet everywhere") strictly
  decreases; implement the round-driver with `termination_by`/`decreasing_by`.
- **Indexed families, gently**: G-Counter state is `Fin R → Nat` (R = number
  of replicas), giving a first taste of dependent-indexed data plus `funext`.

**Not assumed, not used:** Mathlib (forbidden — series rule), Lake project
structure (companion compiles with bare `lean Crdt.lean`), any networking.
All "networks" are simulated in IO or modeled as inductive traces.

---

## 3. Annotated chapter outline

Numbering below is *intent*; the manuscript must use `\label`/`\ref` for every
cross-reference (see §5). Each chapter follows the series rhythm:
**theory sections → "Computation Interlude" (#eval demos) → Exercises**.
Difficulty scale for exercises: ★ (warm-up, minutes) ★★ (an evening)
★★★ (long fuse; solutions appendix gives hints, not spoilers).

### Part I — From One Process to Many

**Ch 1. Replicas, Conflicts, and the Price of Coordination**
- *Goal:* motivate. Offline edits, multi-datacenter writes, collaborative
  editing. Show two replicas of a naive `Nat` counter diverging under
  concurrent increments; show that "just ask a leader" costs a round-trip and
  dies with the leader.
- *CAP in one honest page:* state the Gilbert–Lynch (2002) formalization —
  in an asynchronous network where messages may be lost (partitions), no
  system provides both linearizable consistency and availability of every
  request. Explicitly debunk the "pick 2 of 3" folklore: partition tolerance
  is not optional, and consistency is a spectrum. Position CRDTs: choose
  availability, and buy the *strongest convergence guarantee available
  without coordination* — strong eventual consistency (SEC), defined
  informally here, formally in Ch 8.
- *Lean:* minimal — an `#eval` two-replica divergence demo (`Crdt.Intro`).
- *Refutation:* `refute` "last write wins is a merge strategy for free" —
  concrete interleaving where naive overwrite loses an update.
- *Exercises:* (★) enumerate interleavings of 2 increments on 2 replicas;
  (★) classify real systems (git, calendar sync, bank ledger) by CAP corner;
  (★★) Lean proof that overwrite-merge on `Nat` is not commutative (`decide`).

**Ch 2. The Merge Discipline** (recap-and-bridge)
- *Goal:* restate the predecessor's vocabulary as the discipline every replica
  obeys: state in a bounded join-semilattice; queries read state; updates are
  inflationary (`s ≤ update s`); merge = `⊔`. One diagram: propagator cell
  with the network attached (mirror the predecessor's "traditional cell →
  propagator cell" evolution diagram, adding a third row "replica").
- *Key Lean names:* re-derive (do not import) `Crdt.Order.PartialOrder`,
  `Crdt.Order.BoundedJoinSemilattice` (same field names as the predecessor so
  muscle memory transfers), then the ACI toolkit as named theorems:
  `sup_comm`, `sup_assoc`, `sup_idem`, `sup_bot_left`, `le_iff_sup_eq`,
  `sup_mono`. Define `Inflationary (f : α → α) : Prop := ∀ s, s ≤ f s` and
  prove `sup_inflationary_left : ∀ v s, s ≤ s ⊔ v`.
- *Definition box:* **state-based CRDT** = `(σ, ⊑, ⊔, ⊥)` bounded
  join-semilattice + inflationary update functions + query functions
  (no monotonicity demanded of queries — foreshadow Ch 4).
- *Interlude:* replay a predecessor propagator example, then run the same
  lattice as two "replicas" merging — same code, new reading.
- *Exercises:* (★) `sup_idem` from the axioms alone; (★) `le_iff_sup_eq`;
  (★★) product of semilattices is a semilattice — load-bearing for PN-Counter.

### Part II — The Replica Zoo
Every zoo chapter has the same skeleton: informal story → wrong design +
refutation → right design → semilattice instance (the proof) → inflationary
update proof → interlude → exercises. Say this skeleton out loud in Ch 3 so
readers know the drill.

**Ch 3. Counting Without Coordination: the G-Counter**
- *Refutations (two, both `decide`-checked):*
  `refute` "a distributed counter is a `Nat` with merge = max" — two replicas
  each increment once; max gives 1, truth is 2 (undercounts);
  `refute` "then use merge = (+)" — addition is not idempotent; duplicated
  delivery double-counts. These two failures *derive* the design: keep
  per-replica counts, merge pointwise max.
- *Key Lean names:* `Crdt.GCounter.ReplicaId := Fin R` (R a fixed parameter);
  `GCounter R := Fin R → Nat`; instance `BoundedJoinSemilattice (GCounter R)`
  with `sup g h := fun i => Nat.max (g i) (h i)`, `bot := fun _ => 0`
  (uses `funext` — first appearance, explain it); `increment (i) (g)`;
  `value g := (List.finRange R).foldl (fun a i => a + g i) 0`;
  theorems `increment_inflationary`, `merge_increment_le`
  (`increment i g ⊑ g ⊔ increment i g'` style lemmas),
  `value_le_value_of_le` (value *is* monotone here — contrast with Ch 4).
- *Interlude:* three simulated replicas, out-of-order merges, `#eval value`.
- *Exercises:* (★) prove `increment` at distinct indices commutes;
  (★★) executable `GCounter` as `List Nat` with `zipWith Nat.max`, prove it
  agrees with the functional model on length-R lists; (★★★) prove
  `value (g ⊔ h) ≤ value g + value h` and exhibit strictness (`decide`).

**Ch 4. The PN-Counter and the Query/State Split**
- *Goal:* decrements. State = pair of G-Counters (P, N); value = `(P : Int) − N`.
  The chapter's real lesson: **state is monotone, queries need not be** — the
  lattice disciplines what is *remembered*, not what is *reported*.
- *Refutation:* `refute` "the CRDT's value is monotone" — decrement lowers
  `value` while state strictly grows. This dissolves a common confusion.
- *Key Lean names:* `PNCounter R := GCounter R × GCounter R` (semilattice
  instance via the Ch 2 product instance — restated in the text, since
  exercises can't be load-bearing); `incr`, `decr`,
  `value : PNCounter R → Int`; `decr_inflationary`, `value_merge_ne_max`.
- *Exercises:* (★) `value ⊥ = 0`; (★★) a `clampedValue` query that reports 0
  while true value is negative — seed for Ch 13; (★★) bounded counter
  attempt — mark "finish after Ch 13" (forward-dependency rule).

**Ch 5. Sets That Only Grow: G-Set and 2P-Set**
- *Representation decision (justify in text):* finite sets are **sorted,
  duplicate-free `List Nat`** (element type fixed to `Nat` for `decide`
  friendliness; a notebox sketches generalizing to any linear order).
  Structural recursion throughout so counterexamples run under `decide`.
- *Workhorse lemma:* `sortedDedup_ext` — two sorted duplicate-free lists with
  the same members are equal. All ACI proofs for `union` reduce to membership
  logic through it. This is one of the hardest proofs (see §4) — budget a full
  section for it; it is also excellent structural-induction pedagogy.
- *Key Lean names:* `Crdt.GSet.SList` (subtype or structure with `sorted` +
  `nodup` invariants), `union`, `insertS`, `memS`;
  `union_comm`, `union_assoc`, `union_idem` via `sortedDedup_ext`;
  instance `BoundedJoinSemilattice SList` with `⊑` = subset.
- *2P-Set:* pair (adds, tombstones); `mem e s := e ∈ s.adds ∧ e ∉ s.tombs`.
  **Tombstone cost** section: tombstones grow forever; removed ≠ gone.
- *Refutations:* `refute` "remove-by-deletion is monotone" (deletion moves
  down the lattice; a merge resurrects the element — show it);
  `refute` "2P-Set supports re-add" — `decide`-checked trace: add, remove,
  add again; membership stays false. This refutation is the cliffhanger that
  sells Ch 7.
- *Exercises:* (★) `memS` decidability; (★★) `size` is monotone on G-Set;
  (★★) prove 2P-Set remove is inflationary *on state*; (★★★) intersection is
  a meet, and why meet-merge would violate inflation.

**Ch 6. Last Writer Wins: LWW-Register and LWW-Element-Set**
- *Goal:* registers — overwrite semantics recovered *lawfully* by reifying
  time into the state so that merge can order writes.
- *Refutation (first-class, the chapter's pivot):* `refute` "LWW merge with
  bare timestamps is commutative" — on a tie (`t₁ = t₂`, different values),
  `merge a b ≠ merge b a`; `decide`-checked. Fix: totalize the tiebreak with
  the lexicographic pair `(timestamp, replicaId)` — replicaIds are distinct,
  so the order is total on writes that can actually coexist.
- *Key Lean names:* `Crdt.LWW.Stamp := Nat × Fin R` with `stampLt`
  lexicographic; `stampLt_trichotomy` (needs distinct-replica hypothesis for
  strictness — state carefully); `LWWReg (α) := Option (Stamp × α)` with
  merge = max-by-stamp; `merge_comm`, `merge_assoc`, `merge_idem` — note
  these are proved from *linear-order max* laws, a different route to ACI
  than the pointwise/setwise ones: three routes, one algebra (say this).
  `LWWElementSet := (elem → LWWReg Bool)`-style map of add/remove stamps,
  or association list keyed by element; `mem`, `mem_merge` characterization.
- *Notebox:* physical clocks lie (skew, leap seconds); timestamps here are
  logical tokens; Ch 10 builds honest logical time.
- *Exercises:* (★) `merge ⊥ x = x`; (★★) the tie refutation for a 3-way
  merge; (★★★) "remove-wins" tie variant of LWW-Element-Set — prove it also
  converges; observe semantics change while convergence holds: convergence ≠ intent.

**Ch 7. The OR-Set: Add Wins**
- *Goal:* fix 2P-Set's re-add and LWW-Set's arbitration with **unique tags**:
  each add produces a fresh tag `(replicaId, localCounter)`; remove tombstones
  only the tags it has *observed*. A later add carries a new tag no tombstone
  covers — re-add works; concurrent add/remove resolves add-wins.
- *Key Lean names:* `Crdt.ORSet.Tag := Fin R × Nat`;
  `ORSet := SList (Elem × Tag) × SList (Elem × Tag)` (adds, tombstones — pairs
  encoded to fit the sorted-list machinery; give `Nat` pairing or a
  lexicographic order on pairs); `add`, `remove`, `mem e s := ∃ t, (e,t) ∈
  adds ∧ (e,t) ∉ tombs`; semilattice instance is pairwise G-Set (free);
  **the hard theorem** `addWins`: in any two-replica scenario where replica A
  does `add e` (fresh tag) and replica B concurrently does `remove e`, after
  merge `mem e = true`. Requires a *freshness invariant* (`WfORSet`:
  tombstones ⊆ ever-issued tags; local counter exceeds all locally issued
  tags) preserved by `add`/`remove`/`merge` — an inductive-invariant proof,
  the reader's first taste of the style Ch 8–9 need. See §4 sketch.
- *Refutation:* `refute` "tags can be reused" — reuse a tag, watch a remove
  from another replica delete a *later* add (`decide`).
- *Interlude:* the full add/remove/re-add trace that broke 2P-Set, now
  passing, plus duplicated-delivery runs.
- *Exercises:* (★) `mem` decidable; (★★) garbage: prove tombstone count is
  monotone (cost is real); (★★★) optimized OR-Set sketch (keep only maximal
  tags per replica) — mark "finish after Ch 10" (needs version vectors).

### Part III — Convergence

**Ch 8. Multisets, Folds, and the Main Theorem** (the summit; quotients)
- *Goal:* make SEC a theorem. Model: an *execution* delivers to each replica
  a `List σ` of update-states; replica state = `foldJoin : List σ → σ`
  (`foldl (· ⊔ ·) ⊥`). SEC = if two replicas' delivered lists contain the
  same *set* of updates (any order, any multiplicities ≥ 1), their folds are
  equal.
- *Quotient pedagogy (a full section before use):* motivate `Quotient` with
  ℤ as ℕ×ℕ; then `Setoid` for `List.Perm`; `MSet σ := Quotient (permSetoid σ)`;
  lift `foldJoin` with `Quotient.lift` — the obligation *is*
  `foldJoin_perm : l₁ ~ l₂ → foldJoin l₁ = foldJoin l₂`. Note honestly:
  `#print axioms` will now show `Quot.sound`; discuss what that means.
  (Define `List.Perm` inductively ourselves — series rule: understand every
  axiom; stdlib's exists but hand-roll to match the predecessor's ethos, and
  say a margin note points at the stdlib version.)
- *Key Lean names & theorem chain:*
  `foldJoin`, `le_foldJoin_of_mem`, `foldJoin_le` (fold is the lub of the
  list), `foldJoin_perm`, `foldJoin_dup : foldJoin (a :: a :: l) = foldJoin
  (a :: l)`, and the keystone
  `foldJoin_eq_of_same_mems : (∀ x, x ∈ l₁ ↔ x ∈ l₂) → foldJoin l₁ =
  foldJoin l₂` — proved *not* by list surgery but by antisymmetry: each fold
  is ≤ the other via `foldJoin_le` + `le_foldJoin_of_mem`. Then
  `MSet.foldJoin`, and finally
  **`sec_state_based : SameDeliveredSet r₁ r₂ → state r₁ = state r₂`**.
- *Anti-entropy corollary:* merging a peer's whole state = delivering all its
  updates at once: `foldJoin (l₁ ++ l₂) = foldJoin l₁ ⊔ foldJoin l₂`
  (`foldJoin_append`) — gossip is join-propagation; batching is free.
- *Refutation:* `refute` "commutativity+associativity alone suffice" — drop
  idempotence (`(Nat, +)`), duplicate one delivery, folds differ (`decide`).
  Each law is one network sin's antidote — make the table:
  reorder ↔ comm+assoc, duplicate ↔ idem, batch ↔ assoc.
- *Exercises:* (★) `foldJoin_append`; (★★) `MSet.union` well-defined;
  (★★★) converse: if fold is delivery-order-insensitive for all lists, must
  ⊔ be ACI? (hints in solutions).

**Ch 9. Delivery: Gossip, Duplication, and Reordering**
- *Goal:* connect the algebra to an operational model. Define an inductive
  trace semantics: `Event := update r v | send r r' | deliver r msg`;
  `Reachable : Config → Config → Prop`; at-least-once, unordered channels
  (message multiset, delivery nondeterministic). Prove the *eventual
  delivery ⇒ convergence* form of SEC over traces:
  `converged_of_quiescent : Quiescent c → AllDelivered c → ∀ r r', state c r
  = state c r'` by instantiating Ch 8's theorem with an invariant
  "each replica's state = foldJoin of updates it has seen"
  (`state_eq_foldJoin_seen`, preserved by every step — inductive invariant).
- *Well-founded recursion (deliberate gap-rep):* an executable gossip round
  driver `gossipUntilQuiescent` with `termination_by` a measure = total count
  of (update, replica) pairs not yet seen; `decreasing_by` shows each
  productive round strictly shrinks it. Compare explicitly with the
  predecessor's fuel-based `runToFixpoint`: fuel was an IOU; the measure pays
  it — the sequel's technical growth in one contrast.
- *Interlude:* simulate 4 replicas, drop/duplicate/reorder via a seeded
  pseudo-random schedule, `#eval` convergence; then *adversarial* schedules.
- *Exercises:* (★) a trace where states differ pre-quiescence; (★★) `seen`
  is monotone along `Reachable`; (★★★) message loss: convergence still holds
  under an eventual-delivery fairness hypothesis — hints in solutions.

**Ch 10. Time Without Clocks: Version Vectors and Causality**
- *Goal:* a CRDT about CRDTs. `VV R := Fin R → Nat` — literally the G-Counter
  carrier with pointwise max merge (the instance is *shared code*; say so and
  reuse `Crdt.GCounter`'s instance, renaming via `abbrev`). But read the
  order differently: `v ⊑ w` = "w has seen everything v has" = happens-before.
- *Key Lean names:* `VV`, `tick`, `happensBefore v w := v ⊑ w ∧ v ≠ w`,
  `Concurrent v w := ¬ v ⊑ w ∧ ¬ w ⊑ v`; `happensBefore_irrefl/trans`
  (strict partial order); `concurrent_symm`;
  characterization `vv_le_iff : v ⊑ w ↔ ∀ i, v i ≤ w i`.
- *Refutation:* `refute` "version vectors totally order events" — two ticks on
  different replicas are `Concurrent` (`decide` on `Fin 2`). Concurrency is
  not a failure to know; it is a fact about the world.
- *Payoffs:* causal delivery (`deliverable`) — explains LWW's logical-clock
  upgrade, unlocks Ch 7's ★★★ exercise, preps Ch 11's delivery needs.
- *Exercises:* (★) `tick` inflationary; (★★) `VV` merge = lub of causal
  histories; (★★★) dotted version vectors sketch (hints in solutions).

### Part IV — Operations, Systems, and Limits

**Ch 11. Op-Based CRDTs and the Correspondence** (lighter, one chapter)
- *Goal:* the other tradition: ship operations, not states; require causal
  delivery + commuting concurrent ops instead of ACI joins. Keep it honest
  and light: full op-based formalization is a different book.
- *Key Lean names:* `OpCRDT` structure (`apply : Op → σ → σ`,
  `concurrentCommute` law); op-based counter (`apply (incr i)` = add;
  commutes outright, needs no causal order but *does* need exactly-once —
  contrast table with state-based); the **correspondence, formalized for one
  instance**: `opGCounter_simulates : applying op-log = foldJoin of state
  deltas` for the G-Counter (state-based emulation of op-based and back).
  General correspondence stated as a boxed *theorem without Lean proof* —
  flag clearly per series honesty norms (like the predecessor's
  spec-vs-implementation notebox).
- *Refutation:* `refute` "op-based OR-Set tolerates duplicated delivery" —
  duplicated remove-op double-applies; `decide`-checked on a small model.
  Moral: op-based moves the burden from the algebra to the transport.
- *Exercises:* (★) op-based PN-Counter; (★★) show op-counter under
  at-least-once overcounts; (★★★) delta-CRDTs as the midpoint — reading +
  a delta-interval lemma for G-Counter.

**Ch 12. Capstone: A Replicated Store in Lean**
- *Goal:* the payoff build, mirroring the predecessor's capstone style.
  A collaborative shopping list: OR-Set of items + PN-Counter of quantities
  per item (composition of Part II pieces), replicated across N simulated
  replicas with the Ch 9 gossip harness in IO (`Cell`-style mutable replica
  state, `Sim` namespace, seeded scheduler with duplication + reordering
  knobs).
- *Deliverables:* `Crdt.Capstone.Store` (composed semilattice from earlier
  instances — no new proofs; the point is composition is free);
  `demoConvergence : IO Unit` running three adversarial schedules to
  identical final states; the convergence theorem *instantiated* at `Store`
  (`sec_store := sec_state_based (σ := Store) …`) — one line; say loudly
  that the one-line-ness is the whole book.
- *Exercises:* (★) add a store field; (★★) implement "clear list" and
  discover which semantics you accidentally chose; (★★★) swap OR-Set for
  2P-Set and write the user-visible bug report.

**Ch 13. What CRDTs Cannot Do**
- *Goal:* honest limits, light on machinery. (a) SEC is convergence, not
  correctness: converging to a state nobody wanted (LWW data loss) counts.
  (b) Cross-replica invariants: "balance ≥ 0" cannot survive available-
  under-partition writes — the two-replica double-spend as a small formal
  refutation (`refute` "there is a merge for non-negative bank accounts",
  over a tiny model, `decide`/`omega`). (c) When to coordinate: escrow/
  reservations sketch, consensus pointer. (d) Tombstone growth and the
  garbage-collection-needs-coordination irony (closes Ch 5/7 costs).
- *Exercises:* (★) classify app features as CRDT-able or not, with reasons;
  (★★) escrow split bounding the PN-Counter (resolves Ch 4's marked exercise).

### Appendices
- **A. Lean 4 Quick Reference** — carry the predecessor's tables forward,
  add new sections: quotients (`Setoid`, `Quotient.mk/lift/sound/ind`),
  `termination_by`/`decreasing_by`, `funext`, `Fin` idioms, `List.Perm`.
- **B. Selected Solutions** — full solutions for single-answer exercises;
  *hints only* for ★★★ long-fuse ones. Every entry referenced by
  `\ref{ex:...}`, never a hardcoded number (the predecessor hardcoded these —
  known flaw, do not repeat).

---

## 4. Companion file architecture — `Crdt.lean`

One file, `/home/adekau/lean4learning/crdt/Crdt.lean`. Rules (series law):
- Zero dependencies beyond the prelude; compiles with `lean Crdt.lean`
  (toolchain `leanprover/lean4:v4.28.0` per `/home/adekau/lean4learning/lean-toolchain`).
- Zero `sorry`. Structural recursion preferred wherever a `decide`-checked
  counterexample must evaluate; well-founded recursion only where it *is the
  lesson* (Ch 9 driver).
- Namespaces per part/chapter; `#print axioms` audit lines for every headline
  theorem at the end of the file (expect `propext`, `Quot.sound`; flag and
  justify anything else; `sec_state_based` must not use `Classical.choice`
  unless unavoidable — try to keep the main chain constructive).

Namespace map with line estimates (total ≈ 2,300):

| Namespace | Contents | Est. lines |
|---|---|---|
| `Crdt.Order` | PartialOrder, BoundedJoinSemilattice, ACI toolkit, product instance, notation `⊑ ⊔ ⊥` | 160 |
| `Crdt.Intro` | Ch 1 divergence demos | 40 |
| `Crdt.GCounter` | Fin R → Nat, instance, increment, value, refutation models | 180 |
| `Crdt.PNCounter` | product, incr/decr, value, non-monotone-query lemma | 110 |
| `Crdt.SList` | sorted-dedup lists: insertS, union, memS, `sortedDedup_ext`, ACI, instance | 260 |
| `Crdt.GSet` / `Crdt.TwoPSet` | wrappers, tombstones, re-add refutation | 120 |
| `Crdt.LWW` | Stamp lex order, LWWReg, tie refutation, ACI via max, LWW-Element-Set | 190 |
| `Crdt.ORSet` | tags, add/remove/mem, `WfORSet`, `addWins`, reuse refutation | 280 |
| `Crdt.Perm` / `Crdt.MSet` | hand-rolled `List.Perm`, Setoid, Quotient, lifted fold | 200 |
| `Crdt.SEC` | foldJoin lemma chain, `sec_state_based`, `foldJoin_append`, non-idem refutation | 180 |
| `Crdt.Delivery` | trace semantics, invariant, `converged_of_quiescent`, WF gossip driver | 220 |
| `Crdt.VV` | version vectors, happens-before, concurrency, causal delivery | 130 |
| `Crdt.OpBased` | OpCRDT, op-counter, correspondence instance, dup refutation | 140 |
| `Crdt.Capstone` | Store, IO sim harness, demos, `sec_store` | 230 |
| `Crdt.Limits` | bank-account impossibility mini-model | 60 |
| audits | `#print axioms` block | 30 |

**The 7 hardest proofs, with sketches:**

1. **`SList.sortedDedup_ext`** (two sorted nodup lists, same members ⇒ equal).
   Induction on both lists; head case: each head is the minimum of its member
   set (sortedness), same member set ⇒ equal heads (≤ both ways +
   antisymmetry on Nat); tails then have same members (nodup removes the
   head cleanly from the membership iff). Everything downstream (`union_comm/
   assoc/idem`) becomes membership logic + `simp`. Fiddliest part: clean
   `mem` characterization lemmas for `insertS`/`union` first — write those
   before attempting ext.
2. **`foldJoin_eq_of_same_mems`**. Do NOT induct on permutations-with-
   duplicates. Prove `foldJoin_le : (∀ x ∈ l, x ≤ c) → foldJoin l ≤ c` and
   `le_foldJoin_of_mem : x ∈ l → x ≤ foldJoin l` (both by induction with a
   generalized accumulator: use `foldl` with `foldl_sup_le` helper
   `foldJoin_from : σ → List σ → σ` generalizing the seed — the accumulator
   generalization is the trap; state helpers over arbitrary seed `a`, not
   `⊥`). Then antisymmetry. `foldJoin_perm` falls out as a corollary
   (perm preserves mem) — but also prove it directly by `Perm.rec` for the
   quotient section's pedagogy.
3. **`MSet.foldJoin` well-definedness** (`Quotient.lift` obligation).
   Trivial given #2 — the pedagogy is the point: the reader's first
   `Quotient.lift`, first `Quotient.sound`, first proof by `Quotient.ind`.
   Sketch the toy ℤ example first in the same shapes.
4. **`ORSet.addWins`**. Invariant: `WfORSet s := (∀ (e,t) ∈ s.tombs,
   (e,t) ∈ s.adds) ∧ ∀ (e,(i,k)) ∈ s.adds, k < s.ctr i` (tombstones only
   observed tags; counters dominate issued tags), plus cross-replica
   freshness: A's next tag `(A, ctr A)` is in no other replica's tombs when
   states come from a common execution (sufficient form: every peer's view
   of A's counter is ≤ A's own; prove that view monotone under merge).
   Then the fresh tag ∉ merged tombs, so `mem e (merge sA' sB')` holds.
   Longest proof in the book; prove the two-replica instance completely
   (state the general claim in prose — no hand-wave on the headline itself).
5. **`Delivery.state_eq_foldJoin_seen` preservation** (inductive invariant
   over the trace relation). Case per event constructor; `deliver` case uses
   `foldJoin_append`/`sup` compatibility; `update` case uses inflationary +
   `foldJoin` snoc lemma. Mechanical but long; design the `Config` record so
   `seen` is a plain `List` per replica and equality is at fold level, not
   list level (avoid needing multiset equality in the invariant).
6. **`gossipUntilQuiescent` termination**. Measure
   `μ c := Σ_r (totalUpdates c − |seen r|)` over `List.finRange R`;
   `decreasing_by` needs: a non-quiescent config has some replica missing
   some update, and one gossip round strictly grows some `seen` while never
   shrinking any (`seen` monotonicity from #5's machinery). Keep the driver's
   step *deterministic* (round-robin full-state exchange) so the measure
   argument is local; the nondeterministic adversary lives in the IO sim,
   which stays fuel-based like `runToFixpoint` (say why: IO schedules are
   adversarial; the theorem covers them via Ch 9's relational semantics).
7. **`LWW.merge_assoc` on `Option (Stamp × α)`**. Max-by-lex-order with
   `Option ⊥`; case bash (3 `Option` layers × trichotomy) — tame it by first
   proving `Stamp` is a decidable linear order (`stampLe_total`,
   `stampLe_antisymm` — antisymmetry needs pairs ext) and a reusable
   `maxBy_assoc` lemma over any decidable linear order, then instantiating.
   Teach the "prove the abstract lemma once" move explicitly.

---

## 5. LaTeX / style guide (extracted from the predecessor — match exactly)

**Document:** `\documentclass[12pt, a4paper, openright]{book}`. Copy the
predecessor's preamble wholesale, then extend. Fonts: `fontspec` +
`unicode-math`; Latin Modern Roman/Math; mono `DejaVu Sans Mono`
`[Scale=0.82]` (needed for Lean Unicode `⊑ ⊔ ⊥ ⊤ ∀ →`). Geometry 1in/1.15in;
`microtype`, `setspace` 1.08, `parskip` 6pt.

**Code:** `minted`, style `friendly`; `lean4` blocks: `bgcolor=gray!6,
frame=lines, fontsize=\small, breaklines, linenos, xleftmargin=14pt`; `text`
blocks yellow!8 for program output; inline `\lc{...}` =
`\mintinline{lean4}{...}`.

**Boxes (tcolorbox, libraries `theorems, breakable, skins, most`):**
`defbox` (blue, attached title "Definition — name"), `thmbox` (green, titled),
`exbox` (orange, "Example — name"), `notebox` (yellow, untitled),
`exercisebox` (purple, auto-numbered). **New for this book — `refutedbox`:**
same construction, `colback=red!4, colframe=red!60!black`, attached title
`Refuted — <claim>`; body states the claim, the counterexample, and the
Lean check. Refutations are first-class results: number them or at least
`\label` them (`ref:...`) — they are cited later.

**Exercise numbering (series rule, fixes a predecessor flaw):**
`\newcounter{exercise}[chapter]`, box does `\refstepcounter{exercise}`, and
`\renewcommand{\theexercise}{\thechapter.\arabic{exercise}}` so `\ref` prints
"3.2". EVERY exercise gets `\label{ex:<slug>}`; the Selected Solutions
appendix and any "finish after Chapter N" markers use `\ref{ex:...}` /
`\ref{ch:...}` — hardcoded numbers are forbidden everywhere (chapters:
`\label{ch:...}`, sections `\label{sec:...}`, refutations `\label{ref:...}`).

**Chapter openers:** italic `\begin{quote}` epigraph with attribution
(predecessor style — plain quote environment, NOT the epigraph package).
Sources: Shapiro et al. (2011) for SEC chapters, Lamport for Ch 10,
Gilbert–Lynch/Brewer for Ch 1, Radul–Sussman callback for Ch 2. Verify
quotes are genuine; paraphrase-with-attribution if not verbatim-verifiable.

**Other:** `titlesec` display chapters; `fancyhdr` italic marks + centered
page number; `hyperref` colorlinks (blue links). Theorem environments exist
(`amsthm`, numbered by chapter) but the predecessor mostly uses the boxes;
follow suit. TikZ styles `node/edge/hasseedge` are predefined — reuse for
replica-network diagrams.

**Build:** requires shell escape + Pygments + a Unicode engine:
`latexmk -xelatex -shell-escape from-propagators-to-replicas.tex`
(predecessor is fontspec-based; xelatex or lualatex both fine — pick one and
state it in a comment at the top of the .tex). PDF artifact lives next to the
source like the predecessor's.

---

## 6. Writing-agent brief

### Working title options (Alex decides)
1. *From Propagators to Replicas: Conflict-Free Replicated Data Types in Lean 4*
   (continuity with "From Zero to Propagators"; recommended)
2. *Joins Across the Wire: CRDTs in Lean 4*
3. *From Zero to CRDTs* (series-pattern, but "zero" is now false advertising —
   the book assumes the predecessor)
Subtitle in all cases keeps the series promise line: "Lean 4 code requires no
external libraries beyond the standard prelude."

### Voice notes
Second person, confident, concrete-before-abstract. Key phrases are
*emphasized*; the pivotal sentence of a section often stands alone as its own
paragraph. Definitions arrive only after an example has made them feel
inevitable ("This is precisely the structure of a…"). Noteboxes carry honest
caveats (spec vs. implementation, what's omitted and why). Refutations are
celebrated, not apologized for. No emojis, no exclamation-mark enthusiasm,
no folklore stated as fact. Sample paragraphs in the series voice:

> A replica does not *store a value*; it stores *everything it has heard so
> far* about a value. That sentence should sound familiar — it is the
> propagator cell's manifesto from the previous book, word for word. The only
> thing that has changed is the postal service. Inside one process, a cell's
> inputs arrived on a scheduler we controlled; between replicas, updates
> arrive late, twice, or in the wrong order, and no scheduler in the world
> can promise otherwise. The remarkable fact — the fact this book exists to
> prove — is that the *same* algebraic discipline that made propagator
> networks converge makes replicas agree.

> It is tempting to model a distributed counter as a natural number and
> merge two copies by taking the larger. The temptation survives about one
> experiment. Let replicas $A$ and $B$ each start at $0$ and each observe one
> increment; both now hold $1$, and their merge holds $\max(1,1) = 1$. Two
> events happened; the counter remembers one. The failure is not a bug in
> `max` — `max` is a perfectly good join. The failure is that we joined the
> wrong lattice.

> Notice what the theorem does *not* say. It does not say replicas agree at
> every moment — they demonstrably do not. It does not say the state they
> agree on is the one your users wanted — Chapter \ref{ch:limits} is about
> exactly that gap. It says something narrower and, once you have operated a
> system without it, more precious: replicas that have heard the same news
> hold the same state, no matter who told them, how often, or in what order.

### Order of implementation (companion-first, per chapter)
Per chapter: (1) write the chapter's `Crdt.lean` namespace to completion —
definitions, theorems, refutation models, interlude demos — compiling, zero
sorries; (2) run every `#eval` and paste *actual* outputs into the interlude
(never invent output); (3) write prose around the now-frozen code;
(4) write exercises and verify their solutions in a scratch file (solutions
must compile — predecessor solutions are real Lean; keep that); (5) fold
solution code into Appendix B. Chapter order = book order; build
`Crdt.SList` (Ch 5) and `Crdt.Perm`/`foldJoin` helpers (Ch 8) early if
sequencing pressure appears — Ch 7 and Ch 9 lean on them.

### Verification gates
- `lean Crdt.lean` green after every chapter (single file, bare invocation,
  toolchain v4.28.0 — no lake project needed; do not add one).
- `#print axioms` audit updated as theorems land; any axiom beyond
  `propext`/`Quot.sound` (and `Classical.choice` where explicitly justified)
  is a stop-the-line event.
- Every `decide`-checked refutation must actually elaborate (they are the
  most likely to rot when definitions shift).
- PDF build (`latexmk -xelatex -shell-escape`) at the end of every Part;
  check: exercise numbers render as `chapter.n`, all `\ref`s resolve (grep
  the log for "undefined references"), minted lean4 blocks show correct
  Unicode in the mono font.
- End-of-book: exercises audit — no exercise depends on later-chapter
  machinery unless it carries an explicit "finish after Chapter \ref{ch:…}"
  marker (series rule, learned the hard way).

### Open questions for Alex (decide before or during Part I)
1. **Title** — pick from §6 options (recommendation: option 1).
2. **Version vectors: own chapter or fold into Ch 9?** Plan says own chapter
   (Ch 10) because it pays off three separate threads (LWW clocks, OR-Set
   optimization, op-based causal delivery) and is the cleanest "CRDT about
   CRDTs" moment; fold it into Ch 9 only if page budget bites.
3. **Depth of op-based treatment (Ch 11):** plan proposes correspondence
   *formalized for the G-Counter only*, general theorem stated in prose.
   Alternative: fully formalize the general state↦op emulation (adds ~150
   lines and a chapter's worth of causal-delivery machinery). Decide by
   appetite after Ch 9's trace semantics — the machinery half-exists then.
4. **Element type for sets:** plan fixes `Nat` (decide-friendly, simple).
   Generalizing `SList` over a `LinearOrder α` typeclass is more honest but
   adds typeclass plumbing to every zoo chapter. Decide at Ch 5.
5. **ORSet `addWins` scope:** complete proof for the two-replica scenario
   (plan) vs. general n-replica reachability invariant (hard; maybe a ★★★
   exercise with hints instead).
6. **Capstone shape:** shopping list (OR-Set + PN-Counter map, plan) vs.
   plain replicated counter (smaller). Plan argues the list: composition-is-
   free is the capstone's actual theorem.
7. **Delta-CRDTs:** currently a ★★★ reading exercise in Ch 11; promote to a
   section if the anti-entropy chapter (Ch 9) lands under budget.
8. **Hand-rolled `List.Perm` vs. stdlib's:** plan hand-rolls to honor
   "understand every axiom"; stdlib's `List.Perm` exists and would save ~60
   lines — margin note either way.
