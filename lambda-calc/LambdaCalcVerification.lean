/- ============================================================
   Proofreading verification for lambda_calculus.tex
   ("A Programmer's Guide to Lambda Calculus")

   Toolchain: leanprover/lean4:v4.31.0 (repo toolchain), core only.
   Every Lean listing in the book was extracted here; code kept
   verbatim where possible. Each place the printed code fails on
   this toolchain is reproduced in a comment with the exact error
   and the minimal fix is marked `-- DEVIATION:`.

   Section map (tex line numbers):
     §A  Named interpreter        (ll. 763–785, 975–984, 1705–1834, appendix 7000–7057)
     §B  De Bruijn interpreter    (ll. 2800–3623, appendix 7061–7129)
     §C  Naive/V2 subst stages    (ll. 2994–3102)
     §D  Recursive-descent parser (ll. 7133–7242)
     §E  Defs env + REPL pipeline (ll. 7246–7297, 6331–6337; session ll. 6264–6293)
     §F  Church-encoding math checks (§§9–10 worked examples & solutions)
     §G  STLC type checker        (ll. 4031–4060, appendix 7301–7326)
     §H  Parser combinators       (ll. 5793–6083, 6357–6396)
     §I  System F checker         (ll. 4756–4853)
     §J  Dependent type checker   (ll. 5421–5539, 5610–5625)
     §K  Misc snippets            (ll. 517–531, 4580–4591, 5637)

   Result: compiles clean; 0 sorries. All #guard lines are
   machine-checked claims about the book's printed outputs.
   ============================================================ -/

/- ============================================================
   §A  Named interpreter
   ============================================================ -/
namespace Named

-- ll. 763–768 (verbatim)
inductive Term where
  | var : String → Term            -- a variable carries its name
  | lam : String → Term → Term     -- a lambda carries parameter name + body
  | app : Term → Term → Term       -- an application carries two sub-terms
  deriving Repr, DecidableEq, Inhabited

-- appendix ll. 7009–7014 (verbatim)
def Term.toString : Term → String
  | .var x     => x
  | .lam x e   => s!"(λ{x}. {e.toString})"
  | .app e₁ e₂ => s!"({e₁.toString} {e₂.toString})"

instance : ToString Term := ⟨Term.toString⟩

-- ll. 975–980 (verbatim)
def freeVars : Term → List String
  | .var x     => [x]                                  -- FV(x) = {x}
  | .lam x e   => (freeVars e).filter (· != x)         -- FV(λx.e) = FV(e)\{x}
  | .app e₁ e₂ => (freeVars e₁ ++ freeVars e₂).eraseDups  -- union

-- ll. 1706–1710 / appendix 7021–7025.  As printed, `def freshVar` FAILS:
--   error: fail to show termination for freshVar.go
--   ...  h✝ : candidate ∈ avoid  ⊢ n + 1 < n
-- (`go` recurses on n+1; there is no decreasing measure and none is given).
-- DEVIATION: marked `partial`. (The book's reader hit the same wall: the
-- user's own Base.lean rewrites freshVar with an explicit fuel parameter.)
partial def freshVar (avoid : List String) (base : String := "x") : String :=
  let rec go (n : Nat) : String :=
    let candidate := s!"{base}{n}"
    if candidate ∈ avoid then go (n + 1) else candidate
  if base ∉ avoid then base else go 0

-- ll. 1712–1722 / appendix 7027–7036.  As printed, `def subst` FAILS:
--   error: fail to show termination for subst
--   (Rule 5's recursive call `subst x s (subst y (.var z) e)` is not on a
--    structural subterm; Lean: "Could not find a decreasing measure").
-- DEVIATION: marked `partial`. (User's Base.lean likewise uses `partial def`.)
partial def subst (x : String) (s : Term) : Term → Term
  | .var y     => if y == x then s else .var y         -- Rules 1,2
  | .app e₁ e₂ => .app (subst x s e₁) (subst x s e₂)   -- Rule 6
  | .lam y e   =>
    if y == x then .lam y e                            -- Rule 3: shadowed
    else if y ∉ freeVars s then
      .lam y (subst x s e)                             -- Rule 4: safe
    else
      let z := freshVar (freeVars s ++ freeVars e ++ [x])
      .lam z (subst x s (subst y (.var z) e))          -- Rule 5: rename

-- ll. 1785–1797 / appendix 7038–7049 (verbatim)
def betaStep : Term → Option Term
  | .app (.lam x body) arg => some (subst x arg body)  -- found a redex!
  | .app e₁ e₂ =>
    match betaStep e₁ with
    | some e₁' => some (.app e₁' e₂)
    | none     => match betaStep e₂ with
                  | some e₂' => some (.app e₁ e₂')
                  | none     => none
  | .lam x e => match betaStep e with
               | some e' => some (.lam x e')
               | none    => none
  | _ => none

-- ll. 1815–1821 (verbatim)
def eval (fuel : Nat) (t : Term) : Term :=
  match fuel with
  | 0         => t
  | fuel' + 1 => match betaStep t with
                 | none    => t
                 | some t' => eval fuel' t'

-- ll. 1826–1834: claimed results check out (modulo display: #eval prints the
-- Repr `Term.lam "y" (Term.var "y")`, not the pretty "(λy. y)" shown).
#guard eval 100 (.app (.lam "x" (.var "x")) (.lam "y" (.var "y")))
        == Term.lam "y" (.var "y")
#guard eval 100 (.app (.app (.lam "x" (.lam "y" (.var "x"))) (.var "a")) (.var "b"))
        == Term.var "a"

-- ll. 2929–2938: substituting into K is a no-op (claim verified)
def K := Term.lam "x" (.lam "y" (.var "x"))
#guard subst "x" (.var "a") K == K
-- NB l. 2933 also shows `#eval subst 0 (.bvar 99) K_db` — `K_db` is never
-- defined anywhere in the book.

-- ll. 1450–1487 worked example: (λy. x y)[x := y] must rename the binder.
-- The implementation picks "x0" as the fresh name (text uses z); free y stays free. ✓
#guard subst "x" (.var "y") (.lam "y" (.app (.var "x") (.var "y")))
        == Term.lam "x0" (.app (.var "y") (.var "x0"))

-- Exercise 6.2 (l. 1662) and its "solution" (ll. 6840–6844):
-- the book claims (λf.λx. f (f x)) (λy. y y) "grows without bound ... does
-- not terminate if we try to fully normalize the body". FALSE: it reaches
-- the normal form λx. (x x) (x x) in three normal-order steps:
#guard eval 100 (.app (.lam "f" (.lam "x" (.app (.var "f") (.app (.var "f") (.var "x")))))
                      (.lam "y" (.app (.var "y") (.var "y"))))
        == Term.lam "x" (.app (.app (.var "x") (.var "x"))
                              (.app (.var "x") (.var "x")))

end Named

/- ============================================================
   §B  De Bruijn interpreter
   ============================================================ -/
namespace DeBruijn

-- ll. 2801–2806 (verbatim; the book calls it Expr with `bvar`)
inductive Expr where
  | bvar : Nat → Expr
  | lam  : Expr → Expr
  | app  : Expr → Expr → Expr
  deriving Repr, DecidableEq, Inhabited

-- appendix ll. 7070–7075 (verbatim)
def Expr.toString : Expr → String
  | .bvar n    => s!"{n}"
  | .lam e     => s!"(λ. {e.toString})"
  | .app e₁ e₂ => s!"({e₁.toString} {e₂.toString})"

instance : ToString Expr := ⟨Expr.toString⟩

-- ll. 2892–2896 (verbatim) — compiles; structural recursion is fine here
def shift (d : Int) (c : Nat) : Expr → Expr
  | .bvar n    => if n ≥ c then .bvar (Int.toNat (n + d)) else .bvar n
  | .lam e     => .lam (shift d (c + 1) e)     -- going under a binder: c increases
  | .app e₁ e₂ => .app (shift d c e₁) (shift d c e₂)

-- ll. 3092–3101 (verbatim)
def subst (k : Nat) (s : Expr) : Expr → Expr
  | .bvar n    => if n == k then s else .bvar n
  | .lam e     => .lam (subst (k + 1) (shift 1 0 s) e)
  | .app e₁ e₂ => .app (subst k s e₁) (subst k s e₂)

-- ll. 3321–3323 (verbatim)
def betaReduce (body arg : Expr) : Expr :=
  shift (-1) 0 (subst 0 (shift 1 0 arg) body)

-- ll. 3573–3592 (verbatim)
def step : Expr → Option Expr
  | .app (.lam body) arg => some (betaReduce body arg)
  | .app e₁ e₂ =>
    match step e₁ with
    | some e₁' => some (.app e₁' e₂)
    | none     => match step e₂ with
                  | some e₂' => some (.app e₁ e₂')
                  | none     => none
  | .lam e => match step e with
             | some e' => some (.lam e')
             | none    => none
  | _ => none

def eval (fuel : Nat) (e : Expr) : Expr :=
  match fuel with
  | 0         => e
  | fuel' + 1 => match step e with
                 | none    => e
                 | some e' => eval fuel' e'

-- ll. 3606–3623 (verbatim)
def isValue : Expr → Bool
  | .lam _ => true
  | _     => false

def cbvStep : Expr → Option Expr
  | .app (.lam body) arg =>
    if isValue arg then some (betaReduce body arg)
    else match cbvStep arg with
         | some arg' => some (.app (.lam body) arg')
         | none      => none
  | .app e₁ e₂ =>
    match cbvStep e₁ with
    | some e₁' => some (.app e₁' e₂)
    | none     => match cbvStep e₂ with
                  | some e₂' => some (.app e₁ e₂')
                  | none     => none
  | _ => none

/- Every printed worked trace re-checked mechanically: -/

-- l. 3153: subst 0 (bvar 1) (λ. 1) = λ. 2 ✓
#guard subst 0 (.bvar 1) (.lam (.bvar 1)) == Expr.lam (.bvar 2)
-- ll. 3258–3271: subst 0 (bvar 1) (λ. 0 1) = λ. 0 2 ✓
#guard subst 0 (.bvar 1) (.lam (.app (.bvar 0) (.bvar 1)))
        == Expr.lam (.app (.bvar 0) (.bvar 2))
-- ll. 3335–3345: (λ. 0)(bvar 1) → bvar 1 ✓
#guard betaReduce (.bvar 0) (.bvar 1) == Expr.bvar 1
-- ll. 3361–3374: (λ. 1)(bvar 5) → bvar 0 ✓
#guard betaReduce (.bvar 1) (.bvar 5) == Expr.bvar 0
-- ll. 3384–3396: (λ. λ. 1 0)(bvar 5) → λ. 6 0 ✓
#guard betaReduce (.lam (.app (.bvar 1) (.bvar 0))) (.bvar 5)
        == Expr.lam (.app (.bvar 6) (.bvar 0))
-- ll. 3552–3562: (λ. 0)(bvar 0) → bvar 0 ✓
#guard betaReduce (.bvar 0) (.bvar 0) == Expr.bvar 0
-- ll. 3564–3568 + solution 28 (ll. 6944–6956): (λ. λ. 1)(bvar 0) → λ. 1 ✓
#guard betaReduce (.lam (.bvar 1)) (.bvar 0) == Expr.lam (.bvar 1)
-- ll. 2741–2759 worked example: K I → λ.λ.0 ✓
#guard eval 100 (.app (.lam (.lam (.bvar 1))) (.lam (.bvar 0)))
        == Expr.lam (.lam (.bvar 0))

-- l. 3625–3627: "Test with K I Ω: normal order finds the answer in 2 steps,
-- while call-by-value diverges."  Verified:
def Kc : Expr := .lam (.lam (.bvar 1))
def Ic : Expr := .lam (.bvar 0)
def Om : Expr := .app (.lam (.app (.bvar 0) (.bvar 0))) (.lam (.app (.bvar 0) (.bvar 0)))
def KIO : Expr := .app (.app Kc Ic) Om
#guard ((step KIO).bind step) == some Ic                 -- 2 normal-order steps ✓
#guard (((step KIO).bind step).map step) == some none    -- and I is normal ✓
def iterCbv : Nat → Expr → Option Expr
  | 0, e => some e
  | n+1, e => (cbvStep e).bind (iterCbv n)
#guard (iterCbv 50 KIO).isSome && (iterCbv 50 KIO != some Ic)  -- CBV still spinning ✓

end DeBruijn

/- ============================================================
   §C  The pedagogical substNaive / substV2 stages (ll. 2994–3102)
   All the "wrong on purpose" behaviors shown in the text check out.
   ============================================================ -/
namespace Stages
open DeBruijn

def substNaive (k : Nat) (s : Expr) : Expr → Expr
  | .bvar n    => if n == k then s else .bvar n
  | .app e₁ e₂ => .app (substNaive k s e₁) (substNaive k s e₂)
  | .lam e     => .lam (substNaive k s e)  -- BUG: k and s unchanged

def substV2 (k : Nat) (s : Expr) : Expr → Expr
  | .bvar n    => if n == k then s else .bvar n
  | .app e₁ e₂ => .app (substV2 k s e₁) (substV2 k s e₂)
  | .lam e     => .lam (substV2 (k + 1) s e)  -- FIX 1 only

-- ll. 3005–3015
#guard substNaive 0 (.bvar 5) (.bvar 0) == Expr.bvar 5
#guard substNaive 0 (.bvar 5) (.bvar 3) == Expr.bvar 3
#guard substNaive 0 (.bvar 5) (.app (.bvar 0) (.bvar 1))
        == Expr.app (.bvar 5) (.bvar 1)
#guard substNaive 0 (.bvar 5) (.lam (.bvar 0)) == Expr.lam (.bvar 5)  -- the shown bug ✓
-- ll. 3048–3064
#guard substV2 0 (.bvar 5) (.lam (.bvar 0)) == Expr.lam (.bvar 0)
#guard substV2 0 (.bvar 5) (.lam (.bvar 1)) == Expr.lam (.bvar 5)
#guard substV2 0 (.bvar 1) (.lam (.bvar 1)) == Expr.lam (.bvar 1)     -- the shown bug ✓

end Stages

/- ============================================================
   §D  Recursive-descent parser (appendix ll. 7133–7242)

   The appendix parser DOES NOT COMPILE on v4.31.0. The String API was
   redesigned: `String.Pos` is now string-indexed —
     error: type expected, got (String.Pos : String → Type)
   and `String.get' / next'` moved to `String.Pos.Raw` with `¬atEnd`
   proofs instead of `p < s.endPos`. Every function in the listing
   (PState, skipWS, peek, expect, parseIdent) fails.
   (On the older toolchain the book targeted, `skipWS`'s and
   `parseIdent`'s non-partial `let rec go` over `next'` would also
   need their own termination arguments.)

   DEVIATION: re-implemented with Nat positions over toList, keeping
   the structure (mutual parseExpr/parseLambda/parseApp/parseAtom and
   the grammar are as printed).
   ============================================================ -/
namespace RD
open Named

structure PState where
  input : List Char
  pos   : Nat
  deriving Repr

abbrev ParseResult (α : Type) := Option (α × PState)

def PState.peekC (s : PState) : Option Char := s.input[s.pos]?

partial def skipWS (s : PState) : PState :=
  match s.peekC with
  | some c => if c == ' ' || c == '\t' then skipWS { s with pos := s.pos + 1 } else s
  | none => s

def peek (s : PState) : Option Char := s.peekC

def expect (s : PState) (c : Char) : ParseResult Unit :=
  match s.peekC with
  | some c' => if c' == c then some ((), skipWS { s with pos := s.pos + 1 }) else none
  | none => none

def isIdentStart (c : Char) : Bool := c.isAlpha || c == '_'
def isIdentCont (c : Char) : Bool := c.isAlphanum || c == '_' || c == '\''

partial def parseIdent (s : PState) : ParseResult String :=
  let s := skipWS s
  match s.peekC with
  | some c =>
    if isIdentStart c then
      let rec go (p : Nat) : Nat :=
        match s.input[p]? with
        | some c' => if isIdentCont c' then go (p+1) else p
        | none => p
      let endP := go (s.pos + 1)
      let name := String.ofList (s.input.drop s.pos |>.take (endP - s.pos))
      some (name, skipWS { s with pos := endP })
    else none
  | none => none

mutual
partial def parseExpr (s : PState) : ParseResult Term :=
  let s := skipWS s
  match peek s with
  | some '\\' => parseLambda s
  | _         => parseApp s

partial def parseLambda (s : PState) : ParseResult Term :=
  match expect s '\\' with
  | none => none
  | some (_, s) =>
    let rec parseParams (s : PState) (acc : List String)
        : ParseResult (List String) :=
      match parseIdent s with
      | some (name, s') => parseParams s' (acc ++ [name])
      | none => if acc.isEmpty then none else some (acc, s)
    match parseParams s [] with
    | none => none
    | some (params, s) =>
      match expect s '.' with
      | none => none
      | some (_, s) =>
        match parseExpr s with
        | none => none
        | some (body, s) =>
          let term := params.foldr (fun p acc => Term.lam p acc) body
          some (term, s)

partial def parseApp (s : PState) : ParseResult Term :=
  match parseAtom s with
  | none => none
  | some (first, s) =>
    let rec go (s : PState) (acc : Term) : Term × PState :=
      match parseAtom s with
      | some (next, s') => go s' (Term.app acc next)
      | none => (acc, s)
    let (result, s) := go s first
    some (result, s)

partial def parseAtom (s : PState) : ParseResult Term :=
  let s := skipWS s
  match peek s with
  | some '(' =>
    match expect s '(' with
    | none => none
    | some (_, s) =>
      match parseExpr s with
      | none => none
      | some (e, s) =>
        match expect s ')' with
        | none => none
        | some (_, s) => some (e, s)
  | _ =>
    match parseIdent s with
    | some (name, s) => some (Term.var name, s)
    | none => none
end

def parse (input : String) : Option Term :=
  let s : PState := skipWS { input := input.toList, pos := 0 }
  match parseExpr s with
  | some (term, _) => some term
  | none           => none

#guard parse "\\x. x" == some (Term.lam "x" (.var "x"))
#guard parse "\\f x. f x x" == some
  (Term.lam "f" (.lam "x" (.app (.app (.var "f") (.var "x")) (.var "x"))))
#guard parse "(\\x. x) y" == some (Term.app (.lam "x" (.var "x")) (.var "y"))

end RD

/- ============================================================
   §E  Definitions environment + pipeline + the REPL session
   ============================================================ -/
namespace Pipeline
open Named DeBruijn RD

-- appendix ll. 7247–7256 (verbatim)
def expandDefs (defs : List (String × Term)) : Term → Term
  | Term.var x =>
    match defs.lookup x with
    | some t => t
    | none   => Term.var x
  | Term.lam x e =>
    let defs' := defs.filter (fun (n, _) => n != x)
    Term.lam x (expandDefs defs' e)
  | Term.app e₁ e₂ =>
    Term.app (expandDefs defs e₁) (expandDefs defs e₂)

-- appendix ll. 7258–7282 (verbatim)
def churchDefs : List (String × Term) :=
  let t name := Term.var name
  let l := Term.lam
  let a := Term.app
  [ ("true",  l "t" (l "f" (t "t"))),
    ("false", l "t" (l "f" (t "f"))),
    ("and",   l "p" (l "q" (a (a (t "p") (t "q"))
                               (l "t" (l "f" (t "f")))))),
    ("or",    l "p" (l "q" (a (a (t "p")
                               (l "t" (l "f" (t "t"))))
                               (t "q")))),
    ("not",   l "p" (a (a (t "p")
                        (l "t" (l "f" (t "f"))))
                        (l "t" (l "f" (t "t"))))),
    ("zero",  l "f" (l "x" (t "x"))),
    ("succ",  l "n" (l "f" (l "x"
               (a (t "f") (a (a (t "n") (t "f")) (t "x")))))),
    ("add",   l "m" (l "n" (l "f" (l "x"
               (a (a (t "m") (t "f"))
                  (a (a (t "n") (t "f")) (t "x"))))))),
    ("mul",   l "m" (l "n" (l "f"
               (a (t "m") (a (t "n") (t "f")))))),
    ("id",    l "x" (t "x")),
    ("const", l "x" (l "y" (t "x")))
  ]

-- ll. 6123–6136 / appendix 7284–7297.  As printed FAILS on v4.31:
--   error: Invalid field `indexOf?`: The environment does not contain
--   `List.indexOf?`
-- DEVIATION: `List.idxOf?` (current name).
def toDeBruijn (ctx : List String := []) : Term → Option Expr
  | Term.var x =>
    match ctx.idxOf? x with
    | some i => some (Expr.bvar i)    -- position IS the index
    | none   => none                  -- unbound variable
  | Term.lam x body =>
    match toDeBruijn (x :: ctx) body with
    | some e => some (Expr.lam e)
    | none   => none
  | Term.app e₁ e₂ => do
    let e₁' ← toDeBruijn ctx e₁
    let e₂' ← toDeBruijn ctx e₂
    some (Expr.app e₁' e₂')

-- appendix ll. 7331–7337 (verbatim, modulo the parser deviation)
def evalString (defs : List (String × Term)) (input : String)
    : String := Id.run do
  let some parsed := parse input | return "Parse error"
  let expanded := expandDefs defs parsed
  let some db := toDeBruijn [] expanded | return "Unbound variable"
  let result := eval 10000 db
  s!"{result}"

/- The example REPL session (ll. 6264–6293) — every numeral/boolean output
   printed in the book has its two de Bruijn indices SWAPPED.  Actual
   outputs of the book's own code: -/

#guard evalString churchDefs "\\x. x" == "(λ. 0)"        -- book: (λ. 0) ✓
-- book prints (λ. (λ. (0 (0 (0 1))))); actual numeral 3 is:
#guard evalString churchDefs "succ (succ (succ zero))"
        == "(λ. (λ. (1 (1 (1 0)))))"
-- book prints (λ. (λ. (0 (0 (0 (0 (0 1)))))); actual numeral 5:
#guard evalString churchDefs "add (succ (succ zero)) (succ (succ (succ zero)))"
        == "(λ. (λ. (1 (1 (1 (1 (1 0)))))))"
-- book prints (λ. (λ. 1)) — that is TRUE. `and true false` is FALSE:
#guard evalString churchDefs "and true false" == "(λ. (λ. 0))"

def defsWithTwo : List (String × Term) :=
  match parse "succ (succ zero)" with
  | some t => ("two", expandDefs churchDefs t) :: churchDefs
  | none   => churchDefs
-- book prints (λ. (λ. (0 (0 (0 (0 (0 (0 1)))))); actual numeral 6:
#guard evalString defsWithTwo "mul two (succ two)"
        == "(λ. (λ. (1 (1 (1 (1 (1 (1 0))))))))"

def defsWithTwice : List (String × Term) :=
  match parse "\\f x. f (f x)" with
  | some t => ("apply_twice", expandDefs churchDefs t) :: churchDefs
  | none   => churchDefs
-- book prints (λ. (λ. (0 (0 1)))) and calls it "the Church numeral 2" (l.6292);
-- the actual numeral 2 is:
#guard evalString defsWithTwice "apply_twice succ zero"
        == "(λ. (λ. (1 (1 0))))"

end Pipeline

/- ============================================================
   §F  Church-encoding mathematics, checked through the evaluator
   (§9 definitions and worked examples; §10 Y combinator; solutions 9.1–9.5)
   ============================================================ -/
namespace ChurchChecks
open Named DeBruijn RD Pipeline

private def addDef (ds : List (String × Term)) (n : String) (src : String)
    : List (String × Term) :=
  match parse src with
  | some t => (n, expandDefs ds t) :: ds
  | none => ds

def defs : List (String × Term) := Id.run do
  let mut ds := churchDefs
  ds := addDef ds "pair"   "\\a b f. f a b"                 -- l. 2183
  ds := addDef ds "fst"    "\\p. p true"                    -- l. 2184
  ds := addDef ds "snd"    "\\p. p false"                   -- l. 2185
  ds := addDef ds "iszero" "\\n. n (\\d. false) true"       -- l. 2213
  ds := addDef ds "phi"    "\\p. pair (snd p) (succ (snd p))" -- l. 2253
  ds := addDef ds "pred"   "\\n. fst (n phi (pair zero zero))" -- ll. 2249–2251
  ds := addDef ds "sub"    "\\m n. n pred m"                -- solution 9.3 (l. 6863)
  ds := addDef ds "exp"    "\\m n. n m"                     -- l. 2146
  ds := addDef ds "if"     "\\p a b. p a b"                 -- l. 2066
  ds := addDef ds "one"    "succ zero"
  ds := addDef ds "two"    "succ one"
  ds := addDef ds "three"  "succ two"
  return ds

def n0 := "(λ. (λ. 0))"
def n1 := "(λ. (λ. (1 0)))"
def n2 := "(λ. (λ. (1 (1 0))))"
def n6 := "(λ. (λ. (1 (1 (1 (1 (1 (1 0))))))))"
def n8 := "(λ. (λ. (1 (1 (1 (1 (1 (1 (1 (1 0))))))))))"
def tt := "(λ. (λ. 1))"
def ff := "(λ. (λ. 0))"

#guard evalString defs "iszero zero" == tt        -- worked example l. 2221 ✓
#guard evalString defs "iszero two"  == ff        -- worked example l. 2221 ✓
#guard evalString defs "iszero (succ zero)" == ff -- solution 9.1 ✓
#guard evalString defs "pred three"  == n2        -- Kleene pair trick ✓
#guard evalString defs "pred zero"   == n0        -- l. 2274 (Pred 0 = 0) ✓
#guard evalString defs "sub three two" == n1      -- solution 9.3 ✓
#guard evalString defs "fst (pair one two)" == n1 -- worked example l. 2193 ✓
#guard evalString defs "snd (pair one two)" == n2
#guard evalString defs "exp two three" == n8      -- Exp m n = m^n ✓
#guard evalString defs "and true false" == ff     -- worked example l. 2081 ✓
#guard evalString defs "not false" == tt
#guard evalString defs "or false true" == tt
-- S K K = I (worked example ll. 1570–1589) ✓
#guard evalString defs "(\\f g x. f x (g x)) (\\x y. x) (\\x y. x)" == "(λ. 0)"
-- Add 2 3 = 5 (solution 9.2) ✓ — already checked in §E via the session

-- §10: factorial via Y under normal order (ll. 2480–2506): Fact 3̄ = 6̄ ✓
def factDefs : List (String × Term) := Id.run do
  let mut ds := defs
  ds := addDef ds "Y"    "\\f. (\\x. f (x x)) (\\x. f (x x))"
  ds := addDef ds "F"    "\\self n. if (iszero n) one (mul n (self (pred n)))"
  ds := addDef ds "fact" "Y F"
  return ds
def evalStringFuel (defs : List (String × Term)) (input : String) (fuel : Nat)
    : String := Id.run do
  let some parsed := parse input | return "Parse error"
  let expanded := expandDefs defs parsed
  let some db := toDeBruijn [] expanded | return "Unbound variable"
  return s!"{eval fuel db}"
#guard evalStringFuel factDefs "fact three" 100000 == n6

end ChurchChecks

/- ============================================================
   §G  STLC type checker (ll. 4031–4060)
   ============================================================ -/
namespace STLC

inductive Ty where
  | base  : String → Ty
  | arrow : Ty → Ty → Ty
  deriving Repr, DecidableEq

inductive TExpr where
  | bvar : Nat → TExpr
  | lam  : Ty → TExpr → TExpr    -- annotation on the parameter
  | app  : TExpr → TExpr → TExpr
  deriving Repr, DecidableEq

-- As printed uses `ctx.get? n` — FAILS on v4.31:
--   error: Unknown constant `List.get?`   (removed from core)
-- DEVIATION: `ctx[n]?`.
def typeCheck (ctx : List Ty) : TExpr → Option Ty
  | .bvar n          => ctx[n]?
  | .lam paramTy body =>
    match typeCheck (paramTy :: ctx) body with
    | some bodyTy => some (.arrow paramTy bodyTy)
    | none        => none
  | .app e₁ e₂ => do
    let funTy ← typeCheck ctx e₁
    let argTy ← typeCheck ctx e₂
    match funTy with
    | .arrow paramTy retTy =>
      if paramTy == argTy then some retTy else none
    | _ => none

-- λ(f:A→B). λ(x:A). f x : (A→B)→A→B  (the §12.5 proof-tree example) ✓
#guard typeCheck []
  (.lam (.arrow (.base "A") (.base "B")) (.lam (.base "A") (.app (.bvar 1) (.bvar 0))))
  == some (.arrow (.arrow (.base "A") (.base "B")) (.arrow (.base "A") (.base "B")))
-- self-application rejected ✓
#guard typeCheck [] (.lam (.base "A") (.app (.bvar 0) (.bvar 0))) == none

end STLC

/- ============================================================
   §H  Parser combinators (ll. 5793–6083)

   Presentation-order problems, all reproduced:
   (1) `many1` (l. 5871) uses `>>=`/`pure` two subsections BEFORE the
       Monad instance is defined (l. 5927):
         error: failed to synthesize instance of type class  Bind Parser
   (2) `lamP`/`appP`/`atomP`/`exprP` (ll. 6026–6044) are mutually
       recursive but not wrapped in `mutual`:
         error: Unknown identifier `exprP` / `atomP`
   (3) `appP`'s `atoms.head` (l. 6036) needs a nonemptiness proof:
         error: Application type mismatch: atoms.head has type
         atoms ≠ [] → ?m ... expected Term
   (4) `char`/`satisfy` (ll. 5816–5823) DO NOT BOUNDS-CHECK the position:
       `s.get ⟨pos⟩` past end-of-string returns the DEFAULT Char `'A'`
       (v4.31 `String.get` out-of-range), and `'A'.isAlphanum = true`,
       so `satisfy Char.isAlphanum` keeps succeeding forever and `many`
       diverges (observed: "deep recursion at 'interpreter'"). Unlike
       the recursive-descent parser (§D), the combinators never test
       `pos < s.length`.
   DEVIATIONS: instances moved before their first use; a `mutual`
   block; `atoms.head!`; and bounds-checks added to char/satisfy.
   ============================================================ -/
namespace Combinators
open Named
set_option linter.unusedVariables false
set_option linter.deprecated false   -- keep the book's `s.get ⟨pos⟩` / `String.mk`

def Parser (α : Type) := String → Nat → Option (α × Nat)

-- DEVIATION: `pos < s.length` guard added (book's version loops past EOF)
def char (c : Char) : Parser Char := fun s pos =>
  if pos < s.length && s.get ⟨pos⟩ == c then some (c, pos + 1) else none

def satisfy (p : Char → Bool) : Parser Char := fun s pos =>
  if pos < s.length then
    let c := s.get ⟨pos⟩
    if p c then some (c, pos + 1) else none
  else none

-- DEVIATION: instances (book ll. 5907–5940) must come before many1/spaces/token
instance : Functor Parser where
  map f p := fun s pos =>
    match p s pos with
    | some (a, pos') => some (f a, pos')
    | none           => none

instance : Applicative Parser where
  pure a := fun s pos => some (a, pos)
  seq pf pa := fun s pos =>
    match pf s pos with
    | some (f, pos') =>
      match pa () s pos' with
      | some (a, pos'') => some (f a, pos'')
      | none            => none
    | none => none

instance : Monad Parser where
  bind p f := fun s pos =>
    match p s pos with
    | some (a, pos') => f a s pos'
    | none           => none

instance : Alternative Parser where
  failure := fun _ _ => none
  orElse p q := fun s pos =>
    match p s pos with
    | some r => some r
    | none   => q () s pos

-- ll. 5862–5875 (verbatim; `many` was already marked partial in the book)
partial def many (p : Parser α) : Parser (List α) := fun s pos =>
  match p s pos with
  | none         => some ([], pos)
  | some (a, pos') =>
    match many p s pos' with
    | some (rest, pos'') => some (a :: rest, pos'')
    | none               => some ([a], pos')

def many1 (p : Parser α) : Parser (List α) :=
  p >>= fun first =>
  many p >>= fun rest =>
  pure (first :: rest)

-- ll. 5883–5893 (verbatim)
def spaces : Parser Unit :=
  many (satisfy Char.isWhitespace) >>= fun _ => pure ()

def token (p : Parser α) : Parser α :=
  p >>= fun a =>
  spaces >>= fun _ =>
  pure a

def symbol (c : Char) : Parser Char := token (char c)

-- ll. 6016–6024 (verbatim)
def ident : Parser String := token do
  let chars ← many1 (satisfy fun c => c.isAlphanum || c == '_' || c == '\'')
  pure (String.mk chars)

def keyword (s : String) : Parser Unit := do
  let name ← ident
  if name == s then pure () else failure

-- ll. 6026–6045; DEVIATION: mutual block + atoms.head!
mutual
partial def lamP : Parser Term := do
  let _ ← symbol '\\'
  let params ← many1 ident
  let _ ← symbol '.'
  let body ← exprP
  pure (params.foldr Term.lam body)

partial def appP : Parser Term := do
  let atoms ← many1 atomP
  pure (atoms.tail.foldl Term.app atoms.head!)   -- DEVIATION: head → head!

partial def atomP : Parser Term :=
  (do let _ ← symbol '('; let e ← exprP; let _ ← symbol ')'; pure e)
  <|> (do let name ← ident; pure (Term.var name))

partial def exprP : Parser Term := lamP <|> appP
end

def runP (p : Parser α) (s : String) : Option α := (p s 0).map (·.1)

#guard runP exprP "\\x. x" == some (Term.lam "x" (.var "x"))
#guard runP exprP "(\\x. x) y" == some (Term.app (.lam "x" (.var "x")) (.var "y"))
#guard runP exprP "f x y" == some (Term.app (.app (.var "f") (.var "x")) (.var "y"))

-- try_ (ll. 6075–6079, verbatim; admittedly a no-op in this simple model)
def try_ (p : Parser α) : Parser α := fun s pos =>
  match p s pos with
  | some r => some r
  | none   => none

-- The typed-syntax sketch (ll. 6341–6396); Ty/typed Term as printed;
-- DEVIATION: mutual block and a body parser (the book's typedLamP calls an
-- `exprP` for the typed language that is never defined).
inductive Ty2 where
  | nat  : Ty2
  | bool : Ty2
  | arr  : Ty2 → Ty2 → Ty2
  deriving Repr, DecidableEq

inductive TTerm where
  | var : String → TTerm
  | lam : String → Ty2 → TTerm → TTerm     -- now: λ(x : T). body
  | app : TTerm → TTerm → TTerm
  deriving Repr, DecidableEq, Inhabited     -- Inhabited: for atoms.head! in tappP

mutual
partial def atomTyP : Parser Ty2 :=
  (do keyword "Nat"; pure .nat)
  <|> (do keyword "Bool"; pure .bool)
  <|> (do let _ ← symbol '('; let t ← typeP; let _ ← symbol ')'; pure t)

partial def typeP : Parser Ty2 := do
  let lhs ← atomTyP
  (do let _ ← token (char '-' >>= fun _ => char '>') -- parse "->"
      let rhs ← typeP                                 -- right-recursive!
      pure (.arr lhs rhs))
  <|> pure lhs
end

partial def typedParam : Parser (String × Ty2) := do
  let name ← ident
  let _ ← symbol ':'
  let ty ← typeP
  pure (name, ty)

mutual
partial def typedLamP : Parser TTerm := do
  let _ ← symbol '\\'
  let params ← many1 (do
    let _ ← symbol '('
    let p ← typedParam
    let _ ← symbol ')'
    pure p)
  let _ ← symbol '.'
  let body ← texprP
  pure (params.foldr (fun (name, ty) acc => .lam name ty acc) body)

partial def tappP : Parser TTerm := do
  let atoms ← many1 tatomP
  pure (atoms.tail.foldl TTerm.app atoms.head!)

partial def tatomP : Parser TTerm :=
  (do let _ ← symbol '('; let e ← texprP; let _ ← symbol ')'; pure e)
  <|> (do let name ← ident; pure (TTerm.var name))

partial def texprP : Parser TTerm := typedLamP <|> tappP
end

#guard runP texprP "\\(x : Nat). x" == some (TTerm.lam "x" .nat (.var "x"))
#guard runP typeP "Nat -> Nat -> Bool"
        == some (Ty2.arr .nat (.arr .nat .bool))   -- right-associative ✓

end Combinators

/- ============================================================
   §I  System F (ll. 4756–4853)

   `FTy.subst` as printed DOES NOT COMPILE:
     error: fail to show termination for SF.FTy.subst
   Root cause: `t₁.subst k s` does NOT mean "substitute inside t₁".
   Generalized dot notation inserts the receiver at the FIRST explicit
   argument of type FTy — which is the replacement parameter `s`, not
   the subject. So `t₁.subst k s` elaborates to `FTy.subst k t₁ s`
   (t₁ becomes the replacement, s the subject): the recursion never
   shrinks, and the semantics are inverted. The call site
   `bodyTy.subst 0 ty` (l. 4824) has the same inversion.
   DEVIATION: recursive calls and call sites written out fully.
   ============================================================ -/
namespace SystemF

inductive FTy where
  | tvar  : Nat → FTy                   -- type variable (de Bruijn)
  | base  : String → FTy                -- base types like Nat, Bool
  | arrow : FTy → FTy → FTy             -- τ₁ → τ₂
  | forall_ : FTy → FTy                 -- ∀α. τ  (α is index 0 in τ)
  deriving Repr, DecidableEq

inductive FExpr where
  | bvar  : Nat → FExpr
  | lam   : FTy → FExpr → FExpr
  | app   : FExpr → FExpr → FExpr
  | tlam  : FExpr → FExpr
  | tapp  : FExpr → FTy → FExpr
  deriving Repr

-- verbatim (dot notation is harmless here: the subject IS the first FTy arg)
def FTy.shift (d : Int) (c : Nat) : FTy → FTy
  | .tvar n      => if n ≥ c then .tvar (Int.toNat (n + d)) else .tvar n
  | .base s      => .base s
  | .arrow t₁ t₂ => .arrow (t₁.shift d c) (t₂.shift d c)
  | .forall_ t   => .forall_ (t.shift d (c + 1))

def FTy.subst (k : Nat) (s : FTy) : FTy → FTy
  | .tvar n      => if n == k then s
                     else if n > k then .tvar (n - 1) else .tvar n
  | .base s      => .base s
  | .arrow t₁ t₂ => .arrow (FTy.subst k s t₁) (FTy.subst k s t₂)  -- DEVIATION: was t₁.subst k s
  | .forall_ t   => .forall_ (FTy.subst (k + 1) (s.shift 1 0) t)  -- DEVIATION: was t.subst ...

-- checker as printed except ctx[n]? (List.get? removed) and the subst call
def fTypeCheck (ctx : List FTy) : FExpr → Option FTy
  | .bvar n       => ctx[n]?                       -- DEVIATION: was ctx.get? n
  | .lam ty body  =>
    match fTypeCheck (ty :: ctx) body with
    | some bodyTy => some (.arrow ty bodyTy)
    | none        => none
  | .app e₁ e₂   => do
    let funTy ← fTypeCheck ctx e₁
    let argTy ← fTypeCheck ctx e₂
    match funTy with
    | .arrow dom cod => if dom == argTy then some cod else none
    | _              => none
  | .tlam body    =>
    let ctx' := ctx.map (·.shift 1 0)
    match fTypeCheck ctx' body with
    | some bodyTy => some (.forall_ bodyTy)
    | none        => none
  | .tapp e ty    => do
    let eTy ← fTypeCheck ctx e
    match eTy with
    | .forall_ bodyTy => some (FTy.subst 0 ty bodyTy)  -- DEVIATION: was bodyTy.subst 0 ty
    | _               => none

-- ll. 4849–4853 claimed output ✓ (after the fixes)
#guard fTypeCheck [] (.tlam (.lam (.tvar 0) (.bvar 0)))
        == some (.forall_ (.arrow (.tvar 0) (.tvar 0)))
-- instantiation: (Λα. λ(x:α). x) [Nat] : Nat → Nat ✓
#guard fTypeCheck [] (.tapp (.tlam (.lam (.tvar 0) (.bvar 0))) (.base "Nat"))
        == some (.arrow (.base "Nat") (.base "Nat"))

end SystemF

/- ============================================================
   §J  Dependent type checker (ll. 5421–5539, 5610–5625)

   Three independent bugs in the printed listing:

   (1) `DTerm.subst` — same dot-notation inversion as §I; as printed it
       fails termination, and `body.subst 0 arg` (whnf, l. 5463) and
       `cod.subst 0 e₂` (l. 5512, the line the book celebrates as "the
       magic line") actually substitute the SUBJECT into the ARGUMENT.
       DEVIATION: calls written out fully, correctly oriented.

   (2) `whnf` does not reduce the head of nested applications:
       ((λA.λB.A) X) Y is left untouched, so `beq`/`dTypeCheck` wrongly
       treat reducible types as stuck. Demonstrated below.

   (3) The variable case `ctx.get? n` returns the stored annotation
       WITHOUT shifting it into the current scope. The looked-up type
       must be shifted up by n+1. With the printed code,
         dTypeCheck [] polyId = some (pi univ (pi (bvar 0) (bvar 0)))
       i.e. Π(A:Type). Π(x:A). x  — the codomain refers to x itself —
       whereas the book claims (l. 5537)
         some (pi univ (pi (bvar 0) (bvar 1)))   -- Π(A:Type). Π(x:A). A.
       The book's claimed outputs match only the FIXED checker.
   ============================================================ -/
namespace Dependent

inductive DTerm where
  | bvar   : Nat → DTerm
  | app    : DTerm → DTerm → DTerm
  | lam    : DTerm → DTerm → DTerm     -- λ(x:A). e  (A is a term!)
  | pi     : DTerm → DTerm → DTerm     -- Π(x:A). B
  | univ   : DTerm
  deriving Repr, DecidableEq, Inhabited

def DTerm.shift (d : Int) (c : Nat) : DTerm → DTerm
  | .bvar n    => if n ≥ c then .bvar (Int.toNat (n + d)) else .bvar n
  | .app e₁ e₂ => .app (e₁.shift d c) (e₂.shift d c)
  | .lam ty e  => .lam (ty.shift d c) (e.shift d (c + 1))
  | .pi  ty e  => .pi  (ty.shift d c) (e.shift d (c + 1))
  | .univ      => .univ

def DTerm.subst (k : Nat) (s : DTerm) : DTerm → DTerm
  | .bvar n    => if n == k then s
                   else if n > k then .bvar (n - 1) else .bvar n
  | .app e₁ e₂ => .app (DTerm.subst k s e₁) (DTerm.subst k s e₂)               -- DEVIATION
  | .lam ty e  => .lam (DTerm.subst k s ty) (DTerm.subst (k+1) (s.shift 1 0) e) -- DEVIATION
  | .pi  ty e  => .pi  (DTerm.subst k s ty) (DTerm.subst (k+1) (s.shift 1 0) e) -- DEVIATION
  | .univ      => .univ

-- the book's whnf (argument order corrected; head-reduction gap kept)
partial def DTerm.whnfBook : DTerm → DTerm
  | .app (.lam _ body) arg => (DTerm.subst 0 arg body).whnfBook  -- DEVIATION: was body.subst 0 arg
  | e                      => e

-- DEVIATION (fix for bug 2): whnf must reduce the head first
partial def DTerm.whnf (t : DTerm) : DTerm :=
  match t with
  | .app f a =>
    match f.whnf with
    | .lam _ body => (DTerm.subst 0 a body).whnf
    | f'          => .app f' a
  | e => e

-- Bug 2 demonstrated: ((λ(A:Type).λ(B:Type).A) Type) (Π(_:Type).Type)
def constU : DTerm := .lam .univ (.lam .univ (.bvar 1))
def nested : DTerm := .app (.app constU .univ) (.pi .univ .univ)
#guard DTerm.whnfBook nested == nested   -- stuck: not reduced at all
#guard DTerm.whnf nested == DTerm.univ   -- fixed whnf: reduces to Type ✓

partial def DTerm.beq (a b : DTerm) : Bool :=
  match a.whnf, b.whnf with
  | .bvar n₁,    .bvar n₂    => n₁ == n₂
  | .app f₁ a₁,  .app f₂ a₂  => f₁.beq f₂ && a₁.beq a₂
  | .lam t₁ e₁,  .lam t₂ e₂  => t₁.beq t₂ && e₁.beq e₂
  | .pi  t₁ e₁,  .pi  t₂ e₂  => t₁.beq t₂ && e₁.beq e₂
  | .univ,        .univ        => true
  | _,            _            => false

-- The checker AS PRINTED (modulo compile fixes): lookup does not shift.
partial def dTypeCheckPrinted (ctx : List DTerm) : DTerm → Option DTerm
  | .bvar n    => ctx[n]?                    -- book: ctx.get? n  (bug 3!)
  | .univ      => some .univ
  | .pi a b    => do
    let aTy ← dTypeCheckPrinted ctx a
    guard (aTy.whnf matches .univ)
    let bTy ← dTypeCheckPrinted (a :: ctx) b
    guard (bTy.whnf matches .univ)
    some .univ
  | .lam a body => do
    let aTy ← dTypeCheckPrinted ctx a
    guard (aTy.whnf matches .univ)
    let bodyTy ← dTypeCheckPrinted (a :: ctx) body
    some (.pi a bodyTy)
  | .app e₁ e₂ => do
    let funTy ← dTypeCheckPrinted ctx e₁
    match funTy.whnf with
    | .pi dom cod =>
      let argTy ← dTypeCheckPrinted ctx e₂
      guard (dom.beq argTy)
      some (DTerm.subst 0 e₂ cod)            -- DEVIATION: was cod.subst 0 e₂
    | _ => none

-- DEVIATION (fix for bug 3): shift the looked-up type into current scope
partial def dTypeCheck (ctx : List DTerm) : DTerm → Option DTerm
  | .bvar n    => (ctx[n]?).map (·.shift (Int.ofNat (n+1)) 0)
  | .univ      => some .univ
  | .pi a b    => do
    let aTy ← dTypeCheck ctx a
    guard (aTy.whnf matches .univ)
    let bTy ← dTypeCheck (a :: ctx) b
    guard (bTy.whnf matches .univ)
    some .univ
  | .lam a body => do
    let aTy ← dTypeCheck ctx a
    guard (aTy.whnf matches .univ)
    let bodyTy ← dTypeCheck (a :: ctx) body
    some (.pi a bodyTy)
  | .app e₁ e₂ => do
    let funTy ← dTypeCheck ctx e₁
    match funTy.whnf with
    | .pi dom cod =>
      let argTy ← dTypeCheck ctx e₂
      guard (dom.beq argTy)
      some (DTerm.subst 0 e₂ cod)
    | _ => none

-- ll. 5531–5539
def polyId : DTerm :=
  .lam .univ (.lam (.bvar 0) (.bvar 0))

-- The printed checker does NOT return the book's claimed output:
#guard dTypeCheckPrinted [] polyId
        == some (.pi .univ (.pi (.bvar 0) (.bvar 0)))   -- Π(A:Type).Π(x:A). x  (wrong!)
-- The fixed checker returns exactly what the book claims (l. 5537):
#guard dTypeCheck [] polyId
        == some (.pi .univ (.pi (.bvar 0) (.bvar 1)))   -- Π(A:Type).Π(x:A). A ✓

-- ll. 5618–5624 (kProof): book claims Π(A:Type).Π(B:Type).Π(_:A).Π(_:B). A
def kProof : DTerm :=
  .lam .univ (.lam .univ (.lam (.bvar 1) (.lam (.bvar 1) (.bvar 1))))
-- printed checker: final codomain bvar 1 refers to the `a` binder, not A (wrong):
#guard dTypeCheckPrinted [] kProof
        == some (.pi .univ (.pi .univ (.pi (.bvar 1) (.pi (.bvar 1) (.bvar 1)))))
-- fixed checker: bvar 3 = A, matching the book's stated proposition ✓
#guard dTypeCheck [] kProof
        == some (.pi .univ (.pi .univ (.pi (.bvar 1) (.pi (.bvar 1) (.bvar 3)))))

end Dependent

/- ============================================================
   §K  Miscellaneous snippets
   ============================================================ -/
namespace Misc

-- ll. 517–531 "Lean 4 in 60 Seconds" (verbatim) ✓
inductive MyNat where
  | zero : MyNat
  | succ : MyNat → MyNat

def add : MyNat → MyNat → MyNat
  | .zero,   m => m
  | .succ n, m => .succ (add n m)

def safeDivide (a b : Nat) : Option Nat := do
  if b == 0 then none else some (a / b)

#guard safeDivide 10 2 == some 5
#guard safeDivide 1 0 == none

-- ll. 4580–4591 BHK examples. As printed, `modus_ponens` FAILS:
--   error: type of theorem `modus_ponens` is not a proposition
--     {A : Sort u_1} → {B : Sort u_2} → (A → B) → A → B
-- (auto-implicits are bound at Sort, not Prop; the other three lines
-- happen to work because ∧/∨/∃ force Prop).
-- DEVIATION: declare A B : Prop.
section BHK
variable {A B : Prop}
theorem and_intro (ha : A) (hb : B) : A ∧ B := ⟨ha, hb⟩
theorem or_left (ha : A) : A ∨ B := Or.inl ha
theorem modus_ponens (hab : A → B) (ha : A) : B := hab ha
theorem exists_gt_5 : ∃ n : Nat, n > 5 := ⟨6, by omega⟩
end BHK

-- l. 5637 (verbatim) ✓
theorem identity (A : Prop) (a : A) : A := a

end Misc

/- ============================================================
   §L  Lean 4 Primer appendix — every desugaring example
       (Appendix "A Lean 4 Primer"). All compile; #guards check the
       manual desugarings against the sugar.
   ============================================================ -/
namespace Primer

-- deriving: Repr / DecidableEq / Inhabited generate boilerplate instances
inductive Color where
  | red | green | blue
  deriving Repr, DecidableEq, Inhabited
#guard (Color.red == Color.red)          -- from DecidableEq (BEq)
#guard (Color.red != Color.green)
#guard (default : Color) == Color.red     -- from Inhabited (first ctor)

-- structure + instance (type classes)
structure Point where
  x : Nat
  y : Nat
  deriving Repr, DecidableEq
instance : Add Point where
  add p q := ⟨p.x + q.x, p.y + q.y⟩
#guard ((⟨1,2⟩ : Point) + ⟨3,4⟩) == (⟨4,6⟩ : Point)

-- do / ← over Option ↔ Option.bind ↔ explicit match
def firstTwo (xs : List Nat) : Option (Nat × Nat) := do
  let a ← xs[0]?
  let b ← xs[1]?
  pure (a, b)
def firstTwoBind (xs : List Nat) : Option (Nat × Nat) :=
  xs[0]?.bind fun a =>
  xs[1]?.bind fun b =>
  pure (a, b)
def firstTwoMatch (xs : List Nat) : Option (Nat × Nat) :=
  match xs[0]? with
  | none   => none
  | some a =>
    match xs[1]? with
    | none   => none
    | some b => some (a, b)
#guard firstTwo [10,20,30] == some (10, 20)
#guard firstTwo [10] == none
#guard firstTwo [10,20,30] == firstTwoBind [10,20,30]
#guard firstTwo [10] == firstTwoMatch [10]

-- guard in the Option monad ↔ if/then/else
def evenHalf (n : Nat) : Option Nat := do
  guard (n % 2 == 0)
  pure (n / 2)
def evenHalfManual (n : Nat) : Option Nat :=
  if n % 2 == 0 then pure (n / 2) else none
#guard evenHalf 10 == some 5
#guard evenHalf 7 == none
#guard evenHalf 10 == evenHalfManual 10

-- <|> (Alternative.orElse) ↔ match on the first
def firstSome (a b : Option Nat) : Option Nat := a <|> b
def orElseManual (a b : Option Nat) : Option Nat :=
  match a with | some x => some x | none => b
#guard firstSome none (some 5) == some 5
#guard firstSome (some 3) (some 5) == some 3
#guard firstSome none (some 5) == orElseManual none (some 5)

-- `_ matches _` ↔ a match returning Bool
#guard (some 3 matches Option.some _) == true
#guard (([] : List Nat) matches _ :: _) == false
#guard (some 3 matches Option.some _)
        == (match some 3 with | Option.some _ => true | _ => false)

-- Id.run do + let mut ↔ a fold
def sumTo (n : Nat) : Nat := Id.run do
  let mut acc := 0
  for i in [0:n] do
    acc := acc + i
  return acc
def sumToFold (n : Nat) : Nat := (List.range n).foldl (· + ·) 0
#guard sumTo 5 == 10
#guard sumTo 5 == sumToFold 5

-- partial: opt out of the termination check
partial def collatzLen (n : Nat) : Nat :=
  if n ≤ 1 then 0
  else 1 + collatzLen (if n % 2 == 0 then n / 2 else 3 * n + 1)

-- termination_by: prove it instead of opting out
def log2 : Nat → Nat
  | 0     => 0
  | 1     => 0
  | n + 2 => 1 + log2 ((n + 2) / 2)
  termination_by n => n
  decreasing_by omega
#guard log2 8 == 3
#guard log2 1 == 0

-- induction ↔ the recursor Nat.rec as a term
theorem zero_add_tac (n : Nat) : 0 + n = n := by
  induction n with
  | zero => rfl
  | succ k ih => rw [Nat.add_succ, ih]
theorem zero_add_rec (n : Nat) : 0 + n = n :=
  Nat.rec (motive := fun n => 0 + n = n)
    rfl
    (fun k ih => by rw [Nat.add_succ, ih])
    n

-- cases ↔ match / the recursor with no IH
theorem someOfNe {x : Option Nat} (h : x ≠ none) : ∃ y, x = some y := by
  cases x with
  | none   => exact absurd rfl h
  | some y => exact ⟨y, rfl⟩

-- obtain ⟨…⟩ ↔ Exists.elim / match
theorem obtainDemo (h : ∃ n : Nat, n > 5) : ∃ m : Nat, m > 4 := by
  obtain ⟨n, hn⟩ := h
  exact ⟨n, by omega⟩
theorem obtainDemoElim (h : ∃ n : Nat, n > 5) : ∃ m : Nat, m > 4 :=
  Exists.elim h (fun n hn => ⟨n, by omega⟩)

-- by omega: linear arithmetic over Nat/Int
example (a b : Nat) (h : a + 1 = b) : a < b := by omega
example : ∃ n : Nat, n > 5 := ⟨6, by omega⟩

end Primer

/- ============================================================
   Not reproduced here (nothing executable to check):
   - l. 5350: `zipWith : Vec α n → ...` display — `Vec` does not exist in
     core Lean; illustrative only.
   - ll. 6208–6214 & 6233–6253 (§22 pipeline/repl): use an undefined type
     `Defs`, undefined `parse`-stage names `display`, `printDefs`,
     `parseLetBinding`, and `defs.insert`; the appendix versions (checked
     above in §E) use `List (String × Term)` and cons instead.
   - ll. 6320–6327 `typedPipeline`: pipes the UNTYPED `Expr` produced by
     `toDeBruijn` into `typeCheck`, which takes a `TExpr` — the sketch
     does not typecheck as written (needs an annotated-AST pipeline).
   ============================================================ -/
