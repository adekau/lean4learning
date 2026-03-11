inductive Term where
  | var (n : Nat) : Term
  | lam (body : Term) : Term
  | app (f : Term) (arg : Term) : Term
deriving Repr, DecidableEq, Inhabited

def identityTerm := Term.lam (.var 0) -- λx.x (Identity)
def yToIdentity := Term.lam (.app (.var 0) (.var 1))
#check Term.app identityTerm (.var 1) -- (λx.x) y
#check Term.lam (.app (.var 0) (.var 1)) -- λx.x y (Apply y to identity)

def listDiff.{u} {α : Type u} [BEq α] : List α -> List α -> List α
  | [], _ => []
  | x :: xs, ys => if ys.contains x then listDiff xs ys else x :: listDiff xs ys

def freeVars (depth : Nat := 0) : Term → List Nat
  | .var i     => if i >= depth then [i] else []
  | .lam body  => freeVars (depth + 1) body
  | .app t1 t2 => (freeVars depth t1 ++ freeVars depth t2).eraseDups

-- λλ.(λ.2) 2
#eval freeVars 0 (.lam (.lam (.app (.lam (.var 2)) (.var 2)))) -- result: [2]

def shadowed (lamBoundVar substVar : String) : Bool := substVar == lamBoundVar

-- 11.2. Consider the term λ. 0 1 (which in named form is λx. x y for some free y). If we
--       substitute this into a context that has one more binder above it, the free variable 1 (referring
--       to y) needs to increase by 1 to still point to the same thing. But 0 (the bound variable)
--       must not change. How do you decide which indices to adjust?

-- keep count like in freeVars.
def shift (shiftBy: Int) (count: Nat := 0) : Term -> Term
  | .var n     => if n ≥ count then .var (Int.toNat (n + shiftBy)) else (.var n)
  | .lam body  => .lam (shift shiftBy (count + 1) body)
  | .app e₁ e₂ => .app (shift shiftBy count e₁) (shift shiftBy count e₂)

#eval shift 1 0 (Term.lam (.app (.var 0) (.var 1)))

-- λ.0     (which is λx.x)
-- (λ.0) 1 (which is (λx.x) y, should evaluate to just y)
-- 0[0 := y] := y -- same idx, subst
-- 1[0 := y] := 1 -- diff idx, leave alone
-- (λ.0)[0 := 1] := λ1.(shift ↑1 1) 0
--               := λ1.2 0 == 2
-- (λ.1)[0 := 1] :=

def subst (count : Nat := 0) (a: Term) : Term -> Term
  | .var n     => if n == count then a else .var n
  | .lam body  => .lam (subst (count + 1) (shift 1 0 a) body)
  | .app e₁ e₂ => .app (subst count a e₁) (subst count a e₂)

def betaReduce (body arg : Term) : Term :=
  shift (-1) 0 (subst 0 (shift 1 0 arg) body)

#eval betaReduce (.lam (.var 0)) (.var 2)

def K := Term.lam (.lam (.var 1)) -- λx.λy.x -- K combinator (First)

def betaStep : Term -> Option Term
  | .app (.lam body) arg => some (betaReduce body arg)
  | .app e₁ e₂ =>
    match betaStep e₁ with
      | some e₁' => some (.app e₁' e₂)
      | none     =>
        match betaStep e₂ with
          | some e₂' => some (.app e₁ e₂')
          | none    => none
  | .lam e    =>
    match betaStep e with
      | some e' => some (.lam e')
      | none    => none
  | _ => none

def eval (fuel: Nat) (t: Term) : Term :=
  match fuel with
    | 0         => t
    | fuel' + 1 => match betaStep t with
                    | some t' => eval fuel' t'
                    | none    => t

def res₁ := betaStep (.app K (.var 0))
#eval match res₁ with
 | some e' => betaStep (.app e' (.var 1))
 | none => none

-- K 0 1 == 0
#eval eval 100 (.app (.app K (.var 0)) (.var 1))

-- K 1 0 == 1
#eval eval 100 (.app (.app K (.var 1)) (.var 0))
