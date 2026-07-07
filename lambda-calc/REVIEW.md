# Proofreading review: lambda_calculus.tex

Reviewed 2026-07-06 (full 7,375-line read; every Lean listing extracted and every
claimed reduction / `#eval` output executed against toolchain
leanprover/lean4:v4.31.0, core only — no Mathlib needed). Companion verification
file: `LambdaCalcVerification.lean` (compiles clean via `lake env lean`, **0
sorries**; every fix marked `-- DEVIATION:` with the exact error, and every printed
output claim machine-checked with `#guard`). Line numbers refer to the .tex. Two
hand-typed reader work-throughs, `Base.lean` and `DeBruijnIndices.lean`, corroborate
several findings (noted inline).

## Verdict

The prose theory is in excellent shape: the substitution rules, α/β/η definitions,
the de Bruijn shift/subst/β formulas, Church/Scott encodings, STLC typing rules,
Curry–Howard, the Lambda-Cube tour, and the historical notes are all correct and
unusually well explained for the target reader. Almost every hand-worked reduction
and de Bruijn trace re-computes exactly as printed.

The **Lean code and the interpreter's claimed outputs are not** in the same shape.
Three problems are serious: (1) the flagship REPL session (§22.4) prints numerals and
booleans with **their two de Bruijn indices swapped** and one boolean is the wrong
value — the capstone demo's output is wrong throughout; (2) the celebrated
dependent-type-checker "magic line" and its companions use Lean **dot notation that
silently binds the wrong argument**, so the printed `subst`/`whnf` compute the wrong
thing and fail to compile at all; and (3) the dependent checker's variable lookup
**omits a shift**, so its two headline outputs (the polymorphic identity's type and
the K proof's type) are *not* what the printed code produces — the book shows the
answer of a corrected checker. Beyond these, roughly a third of the listings do not
compile on v4.31 (non-terminating `def`s that need `partial`, removed core API, a
parser that predates the `String.Pos` redesign, and a combinator library whose
pieces are defined out of order and never bounds-check). One exercise solution
(6.2) states a terminating term diverges.

## Math errors

1. **ll. 6264–6293 — the entire REPL example session prints wrong output.** Every
   numeral/boolean in the capstone session has its two de Bruijn indices swapped
   relative to what the book's own evaluator produces. E.g. `succ (succ (succ zero))`
   is printed `(λ. (λ. (0 (0 (0 1)))))`; the code actually yields
   `(λ. (λ. (1 (1 (1 0)))))` (numeral 3 is `λf.λx. f(f(f x))`, so the applied head is
   index 1 and the base is index 0 — the book has them reversed). Same swap for the
   `add` result (l. 6273), `mul two (succ two)` (l. 6280), and `apply_twice succ zero`
   (l. 6288, also mislabeled "the Church numeral 2" at l. 6292). Worse, `and true
   false` is printed `(λ. (λ. 1))` (l. 6283) — that is **TRUE**; the real result is
   `(λ. (λ. 0))` = FALSE. Verified in `LambdaCalcVerification.lean` §E (`#guard`s on
   `evalString`). Fix: regenerate the session block from the actual interpreter.

2. **l. 1662 / ll. 6840–6844 — Exercise 6.2 solution claims a terminating term
   diverges.** The book says `(λf.λx. f (f x)) (λy. y y)` "grows without bound … does
   not terminate if we try to fully normalize the body." It *does* terminate: it
   normalizes in three normal-order steps to `λx. (x x)(x x)`, which is a normal form
   (no redex — `x` is a variable). Verified §A. The term only diverges if the *result*
   is later applied to an argument; normalizing the body itself halts. Fix: state the
   normal form `λx. (x x)(x x)` and clarify that divergence needs a further
   application.

3. **ll. 6852–6853 — Solution 6.5 reasoning is self-contradictory (answer is
   right).** The text says "This matches rule 5 … actually `y ∉ FV(λy.y)` … So rule 4
   applies," with a leftover "Wait—this looks like capture! But it isn't." The final
   answer `λy. (λy.y) y` is correct (rule 4, since `FV(λy.y)=∅`), but the visible
   back-and-forth (an LLM self-correction left in) will confuse the reader. Fix: state
   plainly that `y ∉ FV(λy.y)`, so rule 4 applies, no capture possible.

4. **ll. 6873, 6883–6894 — Solution 11.1 miscounts App rules.** Prose says the S
   combinator tree "requires … two `App` rules (for `x z` and `y z` and combining
   them)"; that describes *three* applications, and the tree drawn directly below
   correctly has three `App` steps. Fix: "three App rules."

## Lean errors

All reproduced on v4.31.0; every fix is in `LambdaCalcVerification.lean`, marked
`-- DEVIATION:`.

5. **ll. 1705–1722 (and appendix 7021–7036) — `freshVar` and `subst` do not
   compile.** Printed as plain `def`. `freshVar.go` recurses on `n+1` with no
   decreasing measure (`fail to show termination … ⊢ n + 1 < n`); `subst`'s rule-5
   call `subst x s (subst y (.var z) e)` is not structural (`Could not find a
   decreasing measure`). Both need `partial` (or a fuel/measure). Direct evidence the
   printed code is broken: the reader's own `Base.lean` writes `partial def subst` and
   a fuel-bounded `freshVar`. Fix: mark both `partial def`, or add
   `termination_by`/fuel.

6. **ll. 5507–5512, 4788–4793 — dependent- and System-F `subst` use dot notation that
   binds the wrong argument; the code fails to compile and is semantically inverted.**
   `FTy.subst`/`DTerm.subst` have signature `(k : Nat) (s : FTy) : FTy → FTy`. The
   recursive calls `t₁.subst k s` and the headline application-case line
   `cod.subst 0 e₂` (l. 5512, which the book calls "the most important line in the
   entire type checker," l. 5518) rely on generalized field notation inserting the
   receiver at the first explicit argument *of matching type*. That argument is the
   **replacement `s`**, not the subject: `cod.subst 0 e₂` elaborates to
   `DTerm.subst 0 cod e₂` — it substitutes `cod` into `e₂`, the opposite of intended,
   and the recursive `t₁.subst k s` never shrinks its subject, so Lean reports
   `fail to show termination for FTy.subst` / `DTerm.subst`. Same defect in `whnf`
   (`body.subst 0 arg`, l. 5463) and every recursive `subst` arm. Fix (verified):
   write the calls in prefix form, `DTerm.subst 0 e₂ cod`, `DTerm.subst k s t₁`, etc.

7. **ll. 5487–5514 vs the claimed outputs at ll. 5537–5539 and 5621–5624 — the
   dependent checker's variable case omits a shift, so its two headline results are
   wrong.** `| .bvar n => ctx.get? n` returns the stored annotation *unshifted*. A
   looked-up type must be shifted by `n+1` to re-enter the current scope. With the
   printed code, `dTypeCheck [] polyId` yields
   `Π(A:Type). Π(x:A). x` = `pi univ (pi (bvar 0) (bvar 0))`, **not** the book's
   claimed `pi univ (pi (bvar 0) (bvar 1))` = `Π(A:Type). Π(x:A). A` (l. 5537). The
   `kProof` output (ll. 5621–5624) is likewise wrong (final codomain points at the
   inner `a`, not `A`). §J of the verification file demonstrates both: a
   `dTypeCheckPrinted` reproducing the book's answer and a fixed `dTypeCheck`
   (`(ctx[n]?).map (·.shift (n+1) 0)`) matching the book's *stated* output. (STLC and
   System F escape this only because their example types have no free type
   variables.) Fix: shift the looked-up type by `n+1`.

8. **ll. 5462–5464 — `whnf` never reduces the head of a nested application.** It only
   fires when the function is *syntactically* a `lam`; `((λ.λ.·) X) Y` is left stuck,
   so `beq` (definitional equality, l. 5467) wrongly treats reducible types as
   unequal. Demonstrated in §J (`whnfBook nested == nested` vs a corrected
   `whnf nested == univ`). Undermines the "type checker is an evaluator" claim for any
   applied type family, though the book's own examples don't exercise it. Fix: recurse
   into the function position, `match f.whnf with | .lam _ b => …`.

9. **Appendix Parser.lean (ll. 7133–7242) does not compile on v4.31.** The
   `String.Pos` redesign makes `structure PState where pos : String.Pos` fail
   (`type expected, got (String.Pos : String → Type)`), and `String.get'/next'` moved
   to `String.Pos.Raw` taking `¬atEnd` proofs instead of `p < s.endPos`. Every
   function (`PState`, `skipWS`, `peek`, `expect`, `parseIdent`) errors. Reimplemented
   over `List Char` + `Nat` in §D, structure preserved; grammar parses correctly. (On
   the book's older toolchain this likely compiled; flagged because the target is
   v4.31.)

10. **Parser-combinator section (ll. 5793–6083) — four defects.**
    (a) `many1` (l. 5871) uses `>>=`/`pure` two subsections *before* the `Monad
    Parser` instance is introduced (l. 5927): `failed to synthesize instance … Bind
    Parser`. (b) `lamP`/`appP`/`atomP`/`exprP` (ll. 6026–6044) are mutually recursive
    but not wrapped in `mutual`: `Unknown identifier exprP` / `atomP`. (c) `appP`'s
    `atoms.head` (l. 6036) needs a nonemptiness proof (`atoms.head : atoms ≠ [] → …`);
    use `head!` or `foldl … atoms.tail`. (d) `char`/`satisfy` (ll. 5816–5823) never
    bounds-check: `s.get ⟨pos⟩` past end-of-input returns the default `Char` `'A'`,
    and `'A'.isAlphanum = true`, so `many (satisfy Char.isAlphanum)` loops forever
    ("deep recursion at 'interpreter'"). The recursive-descent parser (§D) *does* test
    `pos < endPos`; the combinators must too. §H fixes all four (instances first,
    `mutual`, `head!`, `pos < s.length` guards) and the parser then round-trips.

11. **`ctx.get? n` was removed from core (ll. 4048, 4802, 5489; appendix 7314).**
    `typeCheck`/`fTypeCheck`/`dTypeCheck` all call `List.get?`, which no longer exists
    in v4.31 (`Unknown constant List.get?`). Fix: `ctx[n]?`.

12. **`ctx.indexOf? x` was removed (ll. 6125, appendix 7286).** `toDeBruijn` calls
    `List.indexOf?`, gone in v4.31 (`does not contain List.indexOf?`). Fix:
    `ctx.idxOf?`.

13. **ll. 4581–4587 — `modus_ponens` is "not a proposition."** Relying on
    auto-bound implicits, `theorem modus_ponens (hab : A → B) (ha : A) : B := hab ha`
    binds `A B : Sort _`, so Lean rejects it: `type of theorem modus_ponens is not a
    proposition`. (The `and_intro`/`or_left`/`exists_gt_5` lines beside it happen to
    work because `∧`/`∨`/`∃` force `Prop`.) Fix: add `variable {A B : Prop}` or
    annotate.

14. **l. 2933 — `#eval subst 0 (.bvar 99) K_db` references an undefined term.**
    `K_db` is never defined anywhere in the book. (The `subst 0 …` here is also the
    2-arg de Bruijn subst, whereas the named `subst "x" … K` on the same line is the
    3-arg named one — fine, but `K_db` is dangling.)

15. **Cosmetic: `#eval eval …` prints the `Repr`, not the pretty form (ll. 1827,
    1833).** The comments claim `-- Result: (λy. y)` and `-- Result: a`, but with
    `deriving Repr`, `#eval` prints `Term.lam "y" (Term.var "y")` and `Term.var "a"`;
    the `(λy. y)` form needs `IO.println (toString …)`. The values are correct
    (verified §A). Minor.

## Learning gaps

16. **No Lean tactic/desugaring primer — several constructs are used unexplained.**
    The book's own sibling volumes gained a "tactic primer" appendix; this one would
    benefit similarly. Constructs that appear with no introduction for a
    minimal-background reader: the `do`/`←` `Option`-monad plumbing (first used in
    `toDeBruijn`, l. 6132, explained only loosely at l. 6216); `guard` and
    `_ matches _` in the dependent checker (ll. 5495–5497); `Id.run do` with `let mut`
    (used implicitly in the encodings and REPL); the `deriving` mechanics beyond the
    one-paragraph note at ll. 771–783; and `by omega` (l. 4590) presented as if
    obvious. A one-page appendix desugaring `do`/`←`, `<|>`, and `guard` into explicit
    `match`/`Option.bind` would close the biggest gap.

17. **§16.2/§17 — `fun`/`Λ`, `partial`, and `termination_by` promised but the reader
    is left hanging.** The text repeatedly says Lean "requires termination" and
    mentions a "fuel parameter" (l. 534) and even "when you fought with
    `termination_by`" (l. 5402), yet no listing ever shows a `termination_by`/
    `decreasing_by` clause, and the two functions that actually need one (`freshVar`,
    `subst`, finding 5) are printed as if they compile. A reader who types them in
    hits an opaque termination error with no guidance. Add the `partial`/measure the
    code needs and one worked `termination_by`.

18. **The distinction between "reaches a normal form" and "diverges when applied" is
    never made sharp — and finding 2 is a casualty.** Because §6/§8 slide between
    "reduce to normal form" and "evaluate," the Ex. 6.2 solution mistakes a term with
    a perfectly good normal form for a divergent one. A short box: "a term can have a
    normal form yet build a term that loops only once you apply it" would help.

19. **l. 5350 — `Vec … n` is shown in a `#eval`-adjacent listing but is not core
    Lean.** `def zipWith (f : α → β → γ) : Vec α n → Vec β n → Vec γ n` uses `Vec`,
    which does not exist in core; it is illustrative pseudocode. Worth a one-line
    "(schematic; `Vec` is not in core Lean)" so a reader doesn't try to run it.

## Internal inconsistencies (minor)

20. **ll. 740–742 — orphaned sentence fragment.** §"Implementing It: Representing
    Terms" opens mid-thought: "indices, type checking, and ultimately a dependent type
    checker that verifies proofs." with no lead-in — a truncated section intro.

21. **ll. 4356–4372 — duplicated paragraph.** The passage "Before we can understand
    dependent types, we need to understand the philosophical revolution they grew out
    of…" appears twice, once at ll. 4359–4362 and again at ll. 4368–4371, and the
    `\subsection{The Classical View}` (l. 4365) is immediately followed by a
    `\paragraph{The classical view.}` (l. 4373) covering the same ground.

22. **§22.2 pipeline/REPL sketch (ll. 6208–6253) diverges from the appendix it
    claims to assemble.** It uses an undefined type `Defs`, undefined helpers
    `display`, `printDefs`, `parseLetBinding`, and `defs.insert`, whereas the working
    appendix (§E here) uses `List (String × Term)`, `toString`, `splitOn`, and cons.
    And `typedPipeline` (ll. 6320–6327) feeds the *untyped* `Expr` from `toDeBruijn`
    into `typeCheck`, which takes a `TExpr` — the sketch would not type-check as
    written. Presented as illustration, but the mismatch with the runnable appendix
    should be flagged in-text.

23. **l. 1924 — "Standardization" names the wrong theorem.** The statement given
    ("if a term has a normal form, normal-order reduction finds it") is the
    *normalization theorem* (leftmost-reduction / Curry–Feys); the Standardization
    Theorem is the distinct result that any reduction can be reordered into a standard
    one. The attribution and the statement are otherwise fine.

24. **De Bruijn exercise numbering jumps to bare integers "23"–"28"** (solutions
    ll. 6909–6956) where every other section uses the `§.n` form (5.1, 6.1, 9.1, …).
    The `exercise` counter is section-scoped, so these should render as e.g. "17.3";
    the flat numbers suggest a lost `\section` scope or manual numbers. Cosmetic.

## Verification summary

`LambdaCalcVerification.lean` compiles cleanly under
`lake env lean` on leanprover/lean4:v4.31.0, **0 sorries**. It contains every Lean
listing in the book (named interpreter, de Bruijn interpreter, the naive/V2 subst
teaching stages, recursive-descent parser, defs env + pipeline, STLC/System F/
dependent checkers, parser combinators, and the §3/§15/§20 snippets). Each listing
is verbatim except where the book fails to compile; every such spot is marked
`-- DEVIATION:` with the exact error. Findings 5, 6, 9, 10, 11, 12, 13 are
compile-blocking as printed; findings 1, 7, 8 are wrong *outputs* of otherwise
compiling code and are pinned with `#guard`s that show both the book's (wrong)
printed claim and the correct value. Roughly 45 `#guard` assertions machine-check the
reduction traces (all of §7/§11's β-reductions, every de Bruijn worked example and
shift/subst trace, the K I Ω strategy split, the full Church-encoding arithmetic
including `pred`, `sub`, `exp`, pairs, `S K K = I`, and `Y`-combinator factorial
`fact 3 = 6`), the STLC/System F/dependent type outputs, and the parser round-trips.
Fraction of executable claims verified: all of them (every reduction, every `#eval`,
and every type-checker output the book prints). No book listing uses `sorry`; the
0-sorry count is genuine.

## Coverage

Full sequential read of all 7,375 lines. Theory chapters (§§1–10: syntax, FV,
α/β/η, evaluation strategies, Church/Scott encodings, recursion/Y), the "Going
Deeper" part (§§11–21: de Bruijn, STLC, Curry–Howard, intuitionistic logic, System
F/Fω, the Lambda Cube, dependent types, proof-checking, parsing, REPL, the STLC→Lean
landscape, FAQ), the interpreter part, and all four appendices (quick reference,
glossary, exercise solutions, complete implementation) were reviewed. All 40+ Lean
listings extracted and compiled; all worked reductions and every printed interpreter
output recomputed. The reader's `Base.lean`/`DeBruijnIndices.lean` were consulted as
corroborating evidence (they independently use `partial def subst`, confirming
finding 5). TikZ/forest diagrams were read for correctness of their index
annotations (the S-combinator `2 0 (1 0)` diagram and the shift/β "building" figures
are all correct).

## Resolution (2026-07-06)

All findings patched in `lambda_calculus.tex` in place (surgical edits; larger
rewrites only for the REPL session, the dependent checker, and the parser
appendix). PDF rebuilt clean. `LambdaCalcVerification.lean` extended and kept
0-sorry (`lake env lean` exit 0, now **86 `#guard`s**). Line numbers below are
approximate (the file grew from ~7,375 to ~7,700 lines).

**Math errors**

1. **REPL session (§22.4).** Regenerated every output line from the actual
   interpreter values (verification §E): numeral 3 `(λ. (λ. (1 (1 (1 0)))))`,
   numeral 5, numeral 6, `apply_twice succ zero` = `(λ. (λ. (1 (1 0))))`, and
   `and true false` = `(λ. (λ. 0))` (**FALSE**, was wrongly TRUE). Fixed the
   "Church numeral 2" math term (`0(0 1)` → `1(1 0)`) and added a de Bruijn
   index note.
2. **Ex. 6.2.** Rewrote: the term reaches the normal form `λx. (x x)(x x)` in
   three normal-order steps; divergence needs a further application. Cross-links
   the new box (finding 18).
3. **Sol. 6.5.** Removed the "Wait—this looks like capture!" self-correction;
   now states plainly `y ∉ FV(λy.y)`, so rule 4 applies.
4. **Sol. 11.1.** "two App rules" → "three App rules" (one for `x z`, one for
   `y z`, one combining).

**Lean errors**

5. `freshVar`/`subst` → `partial def` (both body and appendix), with a new
   warning box explaining why and pointing to the primer's `termination_by`.
6. Dependent + System-F `subst`/`whnf`: all recursive calls and call sites
   rewritten in prefix form (`DTerm.subst 0 e₂ cod`, etc.); the "magic line"
   prose updated to match. (System-F was already correct in-book.)
7. Dependent checker variable case now shifts: `(ctx[n]?).map (·.shift (Int.ofNat (n+1)) 0)`.
   polyId/kProof outputs now match the printed claims; added the kProof Repr
   output comment (`.bvar 3`).
8. `whnf` rewritten to reduce the function position first (recurses into the head).
9. Appendix `Parser.lean` reimplemented over `List Char` + `Nat` (matches
   verification §D); `parse` seeds `input.toList`. Added a one-line note on the
   `String.Pos` redesign.
10. Parser combinators: (a) added a warning box on instances-before-use ordering
    (standalone `pure`/`bind`/`orElse` are conceptual; the instances make the
    operators available); (b) grammar functions wrapped in `mutual … end`;
    (c) `atoms.head` → `atoms.head!`; (d) `char`/`satisfy` bounds-checked with a
    warning box on the `'A'` default-char loop.
11. `ctx.get? n` → `ctx[n]?` at all four sites (STLC/System-F/dependent body +
    STLC appendix).
12. `ctx.indexOf? x` → `ctx.idxOf? x` (body + appendix).
13. Added `variable {A B : Prop}` before the BHK theorems, with a comment.
14. Defined `K`/`K_db` inline where the dangling `#eval` used them; clarified the
    2-arg vs 3-arg subst.
15. `#eval eval …` comments now show the real `Repr` output; added a note on
    `IO.println (toString …)` for the pretty form (forward ref to Appendix code).

**Learning gaps**

16. Added Appendix **"A Lean 4 Primer"** (`\label{app:primer}`, first appendix),
    with a forward pointer added to §"Lean 4 in 60 Seconds". Entries: `deriving`;
    `structure`/`instance`; `do`/`←` ↔ `Option.bind` ↔ explicit `match`; `guard`
    ↔ `if/else`; `<|>` ↔ match; `_ matches _` ↔ Bool match; `Id.run do`+`let mut`
    ↔ `foldl`; `partial` and `termination_by` (worked `log2`); `induction`/`cases`
    ↔ `Nat.rec (motive := …)` as a term; `obtain ⟨…⟩` ↔ `Exists.elim`/match;
    `by omega` (explicitly *not* magic). All examples compile-checked in
    verification §L.
17. `partial`/`termination_by` now shown (freshVar box + primer `log2`); the
    "fuel is a third option" note ties it to `eval`.
18. Added the "Normal form vs. diverges-when-applied" intuition box at the end of
    §Evaluation Strategies; Ex. 6.2 links to it.
19. `zipWith`/`Vec` snippet annotated "schematic; `Vec` is not in core Lean."

**Internal inconsistencies**

20. Orphaned fragment before §"Implementing It" replaced with a complete lead-in.
21. Removed the duplicated "Before we can understand dependent types…" paragraph
    and the doubled `\paragraph{The classical view.}` under `\subsection{The
    Classical View}`.
22. §22.2 pipeline/REPL sketch: added a warning box mapping the undefined
    `Defs`/`display`/`printDefs`/`parseLetBinding`/`defs.insert` to the concrete
    appendix pieces (`List (String × Term)`, `ToString`, `for`, `splitOn`, cons).
    `typedPipeline`: added a warning that it is schematic and would not
    type-check (untyped `Expr` → `TExpr`); `typedLamP` now calls `texprP` (the
    typed analogue) with a note about the mutual block.
23. "Standardization" theorem renamed "Normalization / Leftmost Reduction," with
    a note distinguishing it from the actual Standardization Theorem.
24. De Bruijn solutions renumbered from bare `23`–`28` to `10.1`–`10.6`
    (matching the author's per-section labels: Church = 9.x, De Bruijn = 10.x,
    STLC = 11.x).

**Version strings (Task E).** None present in the .tex (no Lean version is
printed anywhere); nothing to change.

**Build (Task F).** `latexmk -xelatex -shell-escape lambda_calculus.tex` from
`lambda-calc/`. Installed missing packages `stmaryrd`, `bussproofs`, `forest`.
minted v3 rejected the `[outputdir=build]` package option → removed it.
Pre-existing tcolorbox breakage: `title=#1` mis-parses titles containing `=`
(the six `\begin{workedexample}[$… = …$]` titles threw "Missing $ inserted") →
braced to `title={#1}` in all five box definitions; also fixes commas in titles.
Pinned system DejaVu Sans Mono by path (per sibling books) to avoid dropped
glyphs. Final build: **exit 0, no undefined references, 119 pages** (only two
benign font-shape fallback warnings: italic monospace, bold small-caps).

**Deferred / notes**

- The parser-combinator listings remain conceptual fragments (standalone
  `pure`/`bind`/`orElse` then instances); rather than merge them into one
  compilable block (which would flatten the pedagogy), a warning box states the
  compile-ready ordering. The verification file (§H) holds the runnable version.
- The typed-REPL extension (§22 "Adding Type Annotations") is left as an
  explicitly-flagged sketch; `texprP` and the typed `mutual` block are described,
  not fully printed.
- `#eval (⟨1,2⟩+⟨3,4⟩ : Point)` in the primer shows `⟨4,6⟩` for readability; the
  literal `Repr` is `{ x := 4, y := 6 }` (value verified via `#guard`).
