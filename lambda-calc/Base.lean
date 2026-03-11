inductive Term where
  | var (s : String) : Term
  | lam (var : String) (body : Term) : Term
  | app (f : Term) (arg : Term) : Term
deriving Repr, DecidableEq, Inhabited

def varX := Term.var "x"
def varY := Term.var "y"
def identityTerm := Term.lam "x" varX -- λx.x (Identity)
def yToIdentity := Term.lam "x" (.app varX varY)
#check Term.app identityTerm (.var "y") -- (λx.x) y
#check Term.lam "x" (.app (.var "x") (.var "y")) -- λx.x y (Apply y to identity)

def listDiff.{u} {α : Type u} [BEq α] : List α -> List α -> List α
  | [], _ => []
  | x :: xs, ys => if ys.contains x then listDiff xs ys else x :: listDiff xs ys

def freeVars : Term → List String
  | .var name => [name]
  | .lam var body => listDiff (freeVars body) [var]
  | .app t1 t2 => (freeVars t1 ++ freeVars t2).eraseDups

#eval freeVars (.lam "x" (.lam "y" (.app (.lam "z" (.var "z")) (.var "z"))))

def shadowed (lamBoundVar substVar : String) : Bool := substVar == lamBoundVar

def freshVar (avoid : List String) (base : String := "x") : String :=
  if base ∉ avoid then base
  else go 0 (avoid.length + 1)  -- at most this many tries needed
where
  go (n fuel : Nat) : String :=
    match fuel with
    | 0 => s!"{base}{n}"  -- fallback, can't happen in practice
    | fuel' + 1 =>
      let candidate := s!"{base}{n}"
      if candidate ∈ avoid then go (n + 1) fuel' else candidate

partial def subst (x : String) (a: Term) : Term -> Term
  | .var y => if x == y then a else .var y
  | .lam y body =>
    if y == x then
      .lam y body
    else if y ∉ freeVars a then
      .lam y (subst x a body)
    else
      let newVarName := freshVar (freeVars a ++ freeVars body ++ [x])
      .lam newVarName (subst x a (subst y (.var newVarName) body))
  | .app t₁ t₂ => .app (subst x a t₁) (subst x a t₂)

def K := Term.lam "x" (.lam "y" (.var "x")) -- λx.λy.x -- K combinator (First)

#eval subst "y" (.var "a") (.var "x")
#eval subst "x" (.var "a") (.var "x")
#eval subst "x" (.var "a") (.var "y")

#eval subst "x" (.var "b") (.lam "y" (.var "x")) -- beta step for applying "b" to K

def betaStep : Term -> Option Term
  | .app (.lam x body) arg => some (subst x arg body)
  | .app e₁ e₂ =>
    match betaStep e₁ with
      | some e₁' => some (.app e₁' e₂)
      | none     =>
        match betaStep e₂ with
          | some e₂' => some (.app e₁ e₂')
          | none    => none
  | .lam x e    =>
    match betaStep e with
      | some e' => some (.lam x e')
      | none    => none
  | _ => none

def reduce (fuel: Nat) (t: Term) : Term :=
  match fuel with
    | 0         => t
    | fuel' + 1 => match betaStep t with
                    | some t' => reduce fuel' t'
                    | none    => t

def res₁ := betaStep (.app K (.var "a"))
#eval match res₁ with
 | some e' => betaStep (.app e' (.var "b"))
 | none => none

#eval reduce 100 (.app (.app K (.var "a")) (.var "b"))
