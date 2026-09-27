# Proofreading review: from-propagators-to-replicas.tex

## Second pass (2026-09-27)

**Verdict.** A careful, technically sound book. Every main-text Lean listing was diffed line by line against `Crdt.lean` (compiled on v4.28), and all of them match. The only lines that differ are signature-only excerpts, which the prose flags as such, and Appendix A's pseudo-code. I re-derived the recorded `#eval` outputs (G-Counter, PN-Counter, 2P-Set, LWW, OR-Set, VV, capstone, gossip seeds) by hand from the code, and all of them agree. The errors found are in the prose and are mostly small: miscounts, a wrong refutation title, two inaccurate Lean-terminology claims, a wrong worked-exercise solution and a few internal inconsistencies. No Lean code was changed.

### Fixed — correctness

- **~421** (Ch 1, lost-update table): the prose said B's increment was erased "in the fourth row". The erasing sync ("B syncs from A") is the fifth row. Changed to "fifth row".
- **~680** (Ch 2): "The predecessor book spent three hundred pages". The predecessor `.tex` is about 4,900 lines, shorter than this book (145 pp.). Changed to "The predecessor spent a whole book".
- **~2217** (Ch 5, Refutation `ref:naive-remove`): the title was "Remove-by-deletion is monotone". Deletion (filter) *is* monotone for ⊆. What the Lean refutes is `naiveRemove_not_inflationary`, and the box's own text says "deflationary". Retitled "Remove-by-deletion is inflationary". (The companion docstring still says "monotone"; `Crdt.lean` was left untouched.)
- **~2836–2844** (Ch 6): "the third [route] this book has taken … Three routes, one algebra" contradicted Ch 5 (~2187–2190), which counts pointwise, componentwise and set-theoretic and says "Chapter 6 adds a fourth route". Ch 6 now says "fourth", adds "(and, for the PN-Counter, componentwise, through the product)", and ends "Four routes, one algebra."
- **~3662** (Ch 8 opening): "Part II built five working replicated data types". There are seven (G-Counter, PN-Counter, G-Set, 2P-Set, LWW-Register, LWW-Element-Set, OR-Set), as the preface itself lists. Changed to "seven". "Five times we watched it happen" (five chapter interludes) is correct and was kept.
- **~3793** (Ch 8, quotients): "Lean's honest, definitional `Eq`". `mk 3 5 = mk 10 12` is propositional equality proved via the `Quot.sound` axiom, not a definitional equality. Changed to "built-in".
- **~3882–3883** (Ch 8, `Perm`): the text claimed that without `trans`, "`swap` could only ever disturb the first two positions". With `cons`, a swap can happen at any depth; what is lost is composing more than one swap. Now reads "`cons` and `swap` could only ever exchange a single adjacent pair."
- **~4155–4157** (Ch 8 axioms note): `propext` was described as what "our `funext`-style reasoning has used". `funext` is derived from `Quot.sound`, as the book itself says at ~1301. Changed to "which `simp` and friends have used".
- **~4261** (Ch 8 interlude): "as one, five, and six deliveries". Replica 1 receives `[u₁, u₂, u₃]`, which is three deliveries. Changed to "three, five, and six".
- **~4333** (Ch 9 epigraph): "Peter Deutsch's eight fallacies … (1994)". Deutsch's 1994 list had seven; Gosling added the eighth (~1997). Now reads "the first of the fallacies of distributed computing, as listed by Peter Deutsch (1994)".
- **~4474** (Ch 9): cited `WfORSet`, which does not exist. The invariant is `ORSet.Wf`. Fixed.
- **~4724** (Ch 9 notebox): "The IO simulation there remains fuel-bounded like `runToFixpoint`". `randomGossip` is pure (not IO), and `runToFixpoint` is an unbounded `while` loop with no fuel (Ch 2 ~1010 calls it "fuel-free"). Now reads "The chaotic phase there is fuel-bounded (a fixed number of attempts)".
- **~4877** (Ch 10): claimed "the decidability of the order" flows in from Ch 3 "without a single new proof". The `Decidable (g ⊑ h)` instance is new in the Ch 10 part of the companion, as ~5019 itself says. Removed that item from the list.
- **~6006** (App. B, Ex 1.1 solution): "Four of them lose an update". Enumerating the six program-order-consistent orderings gives final pairs (1,1) ×4 and (0,0) ×2, so *all six* lose an update and none ends in disagreement. Corrected, with the value pairs stated.
- **~6097–6098** (App. B, Ex 5.1): "the `Decidable (x ∈ s)` instance of the main text". That instance appears only in the companion, as the exercise itself says. Changed to "of the companion".
- **~6116–6118** (App. B, Ex 5.3): the solution said the exercise "is `TwoPSet.remove_inflationary`", but the exercise asks for `add` and for composition. Now: mirrors `remove_inflationary`; `add` is the same proof on the first component; composition is `le_trans`.
- **~6137–6138** (App. B, Ex 6.2): "the grouping decides the winner". Both sides of the example are left-nested, and only the inner argument order differs. Changed to "argument order".

### Fixed — prose

- **~264** (preface): the network's "three sins" were listed as "reordering, duplication, redelivery". The Ch 2 and Ch 8 tables pair three sins with three laws as reordering / duplication / *batching*. Aligned the preface to "batching".
- **~1777–1780** (Ex 4.3): missing commas in "…obstruction and Exercise 13.2 which shows…". Changed to "…obstruction, and Exercise 13.2, which shows…".
- **~3669** (Ch 8): the garbled "once and for all state-based CRDTs" became "once and for all, for every state-based CRDT,".

### Flagged, not changed

- **~5279** (Ch 11): "Shapiro et al. (2011), Theorems 2.2–2.3" is cited for the state/op emulation. My recollection is that in the SSS 2011 paper and report, 2.1–2.2 are the CvRDT/CmRDT SEC theorems and the emulation results are 2.3–2.4, but I am not certain. Verify against the paper.
- **~4580–4697** (Ch 9): "Paying off the fuel", "the loop the predecessor could only run on fuel", "`runToFixpoint` took fuel". The predecessor's `runToFixpoint` has no fuel; it is an unbounded `while` loop, as ~1010 says. The text frames this metaphorically ("morally a fuel parameter", ~4581), so I left it. A stricter reading would swap "fuel" for "faith" in ~4672 and ~4697.
- **~827** (Ch 2, table caption): promises that Ch 8 proves "dropping any row breaks convergence". Ch 8 machine-refutes only the loss of idempotence. Non-commutativity is refuted in Ch 1, and there is no associativity refutation. Consider softening the caption.
- **~1154 / ~1137 / ~6020**: "six semilattice axioms" / "prove all six laws". The classes have seven laws (3 `PartialOrder` + 4 `BoundedJoinSemilattice`). "Six … and antisymmetry" in Ex 2.1 adds up to seven, but "all six laws" in Ex 2.3 undercounts by one.
- **~1107** (Ch 2, `replicaReplay` docstring): "Each hears a (consistent) observation" contradicts the code, where only A hears. Left alone because it matches the companion docstring verbatim.
- **~1453**: the `foldl_add_bump` docstring says "induction on `R`", but it inducts on `n`. It matches the companion.
- **~1873**: "in Chapter 6 a single definition will use both [≼ and ⊑] in one line". No such line exists in Ch 6 of the book or the companion. Harmless forward reference, but inaccurate.
- **~2591**: "three layers of `Option`". The register has one `Option` layer; this presumably means the three `Option` arguments of associativity. Reads oddly.
- **~2751**: "these thirty lines". The listed `Option` instances run to about 58 lines.
- **~5852** (App. A): "The five moves" vs Ch 8's "four moves: mk, sound, lift, ind" (~3733, ~3857). The appendix counts `Setoid` and `Quotient` separately and bundles `lift`/`ind`. Minor inconsistency.
- **~4804 vs ~6219**: Ex 9.1 says "Two steps suffice", while the solution says "One step suffices". Both are true, but the pair reads oddly.
- **~5297**: credits `foldJoin_dup` to "Chapter 3". The lemma is from Ch 8; Ch 3 only showed the behaviour experimentally.
- **~5811–5818** (Ex 13.2): "initial credit" is not part of the PN-Counter state as defined. The exercise needs an extra parameter to be stated precisely.
- **Companion `Crdt.lean`**: the axiom-audit comment (line ~2839) repeats the "propext used through funext" misattribution, and the `naiveRemove` docstring says "monotone". Not edited, per instructions to fix the `.tex`.
