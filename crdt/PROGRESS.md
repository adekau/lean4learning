# PROGRESS — From Propagators to Replicas (working notes)

Status ledger for executing PLAN.md. Update after each milestone.

## Decisions taken (defaults from PLAN §6 open questions unless noted)
1. **Title:** *From Propagators to Replicas: Conflict-Free Replicated Data Types in Lean 4* (option 1).
2. **Version vectors:** own chapter (Ch 10).
3. **Op-based:** correspondence formalized for G-Counter only; general theorem in prose box.
4. **Element type for sets:** DEVIATION from plan default — `SList` is generalized over a
   hand-rolled `TotalOrder` typeclass (instances: `Nat`, lex products, `Fin R`) instead of
   fixing `Nat`. Reason: Ch 7 OR-Set needs sorted lists of `(elem, replica, counter)`
   triples; a Nat pairing function would demand injectivity proofs woven through the
   addWins argument, while the lex-product instance is reusable, decide-friendly, and the
   plan itself flags generalization as "more honest" (open question 4, decided at Ch 5).
   The book runs Ch 5 with `Nat` as the concrete instance and noteboxes the class.
5. **addWins scope:** complete proof for two-replica scenario; n-replica general claim in prose.
6. **Capstone:** shopping list (OR-Set items × per-item PN-Counter quantities).
7. **Delta-CRDTs:** ★★★ reading exercise in Ch 11.
8. **List.Perm:** hand-rolled inductive (series ethos); margin note points at stdlib's.
9. **LWW design:** the lattice orders the *entire payload* lexicographically
   (timestamp, replicaId, value) so merge = max of a genuine linear order and ACI holds
   unconditionally on the carrier; text explains the value-tiebreak is unreachable in real
   executions (stamps unique) and exists to totalize the algebra. Tie refutation uses bare
   timestamps as planned. Abstract `maxBy` ACI lemma proved once over a decidable linear
   order (hardest-proof #7 strategy).
10. **Solutions:** compiled inside `Crdt.lean` under `namespace Crdt.Solutions` (guarantees
    zero rot; slight deviation from "scratch file", same guarantee, stronger).

## Toolchain facts (probed, Lean 4.28.0 bare `lean Crdt.lean`)
- Available in core: `List.finRange`, `List.mem_finRange`, `Nat.le_max_left/right`,
  `Nat.max_le` (iff), `List.decidableBEx/BAll`, `Decidable (∀ i : Fin n, p i)` instance,
  `Quotient.mk/lift/sound/ind`, DecidableEq on Option/products.
- NOT in core: `List.length_filter` — hand-roll the strict filter-length lemma for the
  gossip termination measure.
- Build: `lean Crdt.lean` (no lake). PDF: `latexmk -xelatex -shell-escape from-propagators-to-replicas.tex`.

## File map
- `crdt/Crdt.lean` — companion (single file, zero sorry, prelude only).
- `crdt/from-propagators-to-replicas.tex` — the book.
- `crdt/PLAN.md` — the brief. `crdt/PROGRESS.md` — this file.

## Milestones
- [x] 1. Crdt.Order + Crdt.Intro compile
- [x] 2. GCounter + PNCounter compile
- [x] 3. SList + GSet/TwoPSet compile
- [x] 4. LWW compile
- [x] 5. ORSet + addWins compile
- [x] 6. Perm/MSet + SEC compile
- [x] 7. Delivery + VV compile
- [x] 8. OpBased + Capstone + Limits + audits + Solutions compile
      (2,865 lines; zero sorries/warnings; axioms: only propext + Quot.sound,
      NO Classical.choice — main chain constructive; #eval outputs captured in
      scratchpad eval-outputs.txt)
- [x] 9. tex Parts I–II written
- [x] 10. tex Parts III–IV + appendices written
- [x] 11. PDF builds; refs resolve; gates green — DONE 2026-07-04.
      Final artifacts: from-propagators-to-replicas.tex (6,393 lines,
      monolithic, assembled from tex/ fragments now removed) +
      from-propagators-to-replicas.pdf (145 pages). Verification:
      latexmk exit 0, zero LaTeX errors, zero undefined references,
      exercise/refutation numbering renders chapter.n, forward-dependency
      markers present (ex:bounded-counter → ch:limits, ex:optimized-orset
      → ch:vv), `lean Crdt.lean` exit 0, axiom audit = propext +
      Quot.sound only. Build needed: `pip install latexminted` (minted v3
      helper; done on this machine) and unicode-math loaded AFTER amssymb
      (fixed in preamble; the predecessor .tex has the same latent clash).

## LaTeX label registry (SOURCE OF TRUTH — all chapters must use exactly these)
Chapters: ch:intro (1), ch:merge (2), ch:gcounter (3), ch:pncounter (4),
ch:sets (5), ch:lww (6), ch:orset (7), ch:sec (8), ch:delivery (9), ch:vv (10),
ch:opbased (11), ch:capstone (12), ch:limits (13), app:quickref (A), app:solutions (B).

Exercises (label — difficulty — topic; NEVER hardcode numbers, always \ref{ex:...}):
- Ch1: ex:interleavings ★, ex:cap-classify ★, ex:overwrite-not-comm ★★
- Ch2: ex:sup-idem ★, ex:le-iff-sup-eq ★, ex:product-semilattice ★★
- Ch3: ex:increment-comm ★, ex:list-gcounter ★★, ex:value-sup-le ★★★
- Ch4: ex:value-bot ★, ex:clamped-value ★★, ex:bounded-counter ★★ (marked "finish after Chapter~\ref{ch:limits}")
- Ch5: ex:mem-decidable ★, ex:size-monotone ★★, ex:remove-inflationary ★★, ex:meet-merge ★★★
- Ch6: ex:merge-bot ★, ex:three-way-tie ★★, ex:remove-wins ★★★
- Ch7: ex:orset-mem-decidable ★, ex:tombstone-cost ★★, ex:optimized-orset ★★★ (marked "finish after Chapter~\ref{ch:vv}")
- Ch8: ex:foldjoin-append ★, ex:mset-union ★★, ex:aci-converse ★★★
- Ch9: ex:prequiescent ★, ex:seen-monotone ★★, ex:message-loss ★★★
- Ch10: ex:tick-inflationary ★, ex:vv-lub ★★, ex:dotted-vv ★★★
- Ch11: ex:op-pncounter ★, ex:op-overcount ★★, ex:delta-crdt ★★★
- Ch12: ex:store-field ★, ex:clear-list ★★, ex:swap-2pset ★★★
- Ch13: ex:crdt-able ★, ex:escrow ★★ (resolves ex:bounded-counter)

Refutations (refutedbox env, \label{ref:...}): ref:overwrite (Ch1),
ref:max-undercounts + ref:add-overcounts (Ch3), ref:value-monotone (Ch4),
ref:naive-remove + ref:no-readd (Ch5), ref:lww-tie (Ch6), ref:tag-reuse (Ch7),
ref:comm-assoc-not-enough (Ch8), ref:vv-total (Ch10), ref:op-dup (Ch11),
ref:bank (Ch13).

Build assembly: tex chunks in crdt/tex/ (00-preamble, 10-part1 (Ch1–2),
20-part2 (Ch3–7), 30-part3 (Ch8–10), 40-part4 (Ch11–13), 50-appendices,
99-backmatter) concatenated into crdt/from-propagators-to-replicas.tex.
Environments available (defined in preamble): defbox[Name], thmbox[Title],
exbox[Name], notebox, exercisebox[Name] (auto-numbered \thechapter.n, use
\refstepcounter'd label), refutedbox{Claim} (auto-numbered, red), minted lean4
+ text blocks, \lc{inline}, TikZ styles node/edge/hasseedge.
Difficulty marks: exercisebox optional arg carries title text; put ★ marks
at the start of the exercise body as \Stars{1|2|3} macro.

## Revision pass (2026-07-04, after review)
- `text` minted blocks now have `breaklines`/`breakanywhere` — long one-line
  #eval outputs wrap inside the box with a hook-arrow marker instead of
  overflowing the margin.
- CAP is expanded (Consistency/Availability/Partition tolerance) at first
  use, before the Gilbert–Lynch box.
- Un-escaped 25 `\_` inside `\lc{...}` spans (mintinline is verbatim; the
  escapes rendered as literal backslashes). RULE for future edits: never
  escape underscores inside `\lc{}`.
- Split the one over-long inline equation (`finRange_succ`) into breakable
  spans; automated scan confirms zero words past the right margin on all
  145 pages.
- Fixed an inaccurate cross-book reference ("Chapter 2 of the predecessor"
  → the fuel-based loop, no chapter number).
- Owl audit: every load-bearing proof (sorted_ext, addWins, wf_*,
  foldl_add_bump, keystone chain, coherent_step, cost_exchange_lt, maxo,
  lex product) is printed in full; the only elisions are honest,
  explicitly signposted companion pointers (FlatNat case bashes,
  insertS/union membership inductions, filter-length lemmas, findPairAux
  specs). All identifiers cited in prose exist in Crdt.lean (sup_unique is
  a deliberate predecessor citation). Quotient pedagogy verified complete
  (all five moves + toy example + outputs).

## Font-rendering pass (2026-07-05, after review)
- Tofu squares for `⊔` in code: TeX Live/TinyTeX bundles DejaVu Sans Mono
  v2.34, which lacks U+2294 (only that glyph). The preamble now prefers the
  OS copy (`/usr/share/fonts/truetype/dejavu/DejaVuSansMono.ttf`, v2.37+)
  via `\IfFileExists`, falling back to the family name on machines without
  it. All other Lean symbols (⊑ ⟨⟩ ⟦⟧ ≼ ≺ ⊥ …) were already covered.
- Exercise difficulty stars were silently blank: unicode-math maps
  `\bigstar` to U+2605, which Latin Modern Math lacks. `\Stars` (and the
  Appendix B inline stars) now use pifont's `\ding{72}`.
- Authoritative gate added: `grep -c "Missing character"` on the xelatex
  log must be 0 (it is). Run this after any font or symbol change.

## Key #eval outputs (verbatim, for interludes — never invent output)
- propagatorReplay: `sum is 10`
- replicaReplay: `replica A holds 42, replica B holds 42`
- Intro.divergenceDemo: `[("replica A", 2), ("replica B", 1), ("B after sync", 2), ("A after sync", 2), ("ground truth", 3)]`
- GCounter.interlude: `[("replica A", [2, 1, 1], 4), ("replica B", [2, 1, 1], 4), ("replica C", [2, 1, 1], 4)]`
- PNCounter.interlude: `[("A alone", 2), ("B alone", 0), ("A ⊔ B", 2), ("B ⊔ A", 2), ("(A ⊔ B) ⊔ B", 2)]`
- TwoPSet.interlude: `[("1 ∈ A ⊔ B", false), ("1 ∈ B ⊔ A", false), ("3 ∈ A ⊔ B", true), ("re-add at A ⊔ B", false)]`
- LWW.interlude: all reads `some 200` (5 lines; see eval-outputs.txt)
- LWWElementSet.interlude: `[("1 ∈ A ⊔ B", false), ("1 ∈ B ⊔ A", false), ("7 ∈ A ⊔ B", true), ("re-add 1 at t=3", true)]`
- ORSet.interlude: added true / removed false / re-added true / add-wins true / dup true
- IntPairs: `#eval toInt (mk 3 5)` → `-2`; `#eval toInt (neg (mk 3 5))` → `2`
- SEC.interlude: all three replicas `[1, 2, 3]`
- Delivery.simulate 1 / 42 / 2026: chaotic first component differs per seed
  (seed 1: replica 2 missing 4; seed 42: replica 3 = [2,3,4,20]; seed 2026:
  r0=[1,3,4,10], r1=[1,2,4,10,20]); second component always four copies of
  [1, 2, 3, 4, 10, 20]
- VV.interlude: all four entries true
- Capstone.demoConvergence: all three schedules, all three replicas:
  `[(1, (true, 3)), (2, (true, 1)), (3, (false, 0))]`
