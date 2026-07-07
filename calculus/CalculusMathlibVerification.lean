/- ============================================================
   Verified Calculus — Mathlib companion verification file
   From the Natural Numbers to Symbolic Solvers in Lean 4

   This file verifies every MATHLIB-DEPENDENT Lean 4 listing
   printed in calculus/verified-calculus-complete.tex (Part II
   onward: the book deliberately switches from its hand-rolled
   MyReal to Mathlib's `Real` at Chapter 6, as explained in the
   book's "From MyReal to Mathlib" transition passage).

   REQUIREMENTS: Mathlib (leanprover-community/mathlib4,
   rev v4.31.0) on toolchain leanprover/lean4:v4.31.0. This file
   is verified by copying it into a Lake project whose
   lakefile.toml contains

       [[require]]
       name = "mathlib"
       scope = "leanprover-community"
       rev = "v4.31.0"

   and running `lake env lean CalculusMathlibVerification.lean`
   (after `lake exe cache get`; note that all build artifacts,
   including the compiled .olean files, live under `.lake/`).

   Layout:
     VCM        — analysis listings, one section per book chapter:
                  Ch6 sequences, Ch7 functional limits, Ch8
                  continuity, Ch10 derivative, Ch11 rules, Ch15
                  Riemann sketch, Ch16 FTC-2, Ch21 exp series,
                  Ch22 R^n, Ch23 partial derivatives
     VCM36      — Ch. 36: Expr.evalR and the honest diff-
                  correctness lemmas
     VCMPrimer  — Appendix A "A Lean 4 Primer": the Mathlib-tactic
                  examples, compiled (core examples live in
                  CalculusVerification.lean, namespace
                  PrimerAppendix)

   `sorry` appears ONLY where the book itself prints `sorry`
   (marked in the book's prose as exercises/sketches).
   ============================================================ -/
import Mathlib

/- The analysis chapters share one namespace, exactly as the book's
   reader would develop them in one file. Inside it, the book's own
   `ContinuousAt`/`HasDerivAt` shadow Mathlib's; where a listing
   deliberately uses MATHLIB's notion instead (Ch. 16), the book
   writes `_root_.HasDerivAt`. -/
namespace VCM

/- ============================================================
   §Ch6  Sequences and Convergence (book §6.1)
   ============================================================ -/

def SeqLimit (a : Nat -> Real) (L : Real) : Prop :=
  forall eps : Real, eps > 0 ->
    exists N : Nat, forall n : Nat, n > N -> |a n - L| < eps

-- Limits are unique
theorem limit_unique (a : Nat -> Real) (L M : Real)
    (hL : SeqLimit a L) (hM : SeqLimit a M) : L = M := by
  by_contra hne
  have heps : |L - M| / 2 > 0 := by
    have h : L - M ≠ 0 := sub_ne_zero.mpr hne
    positivity
  obtain ⟨N1, hN1⟩ := hL (|L - M| / 2) heps
  obtain ⟨N2, hN2⟩ := hM (|L - M| / 2) heps
  have h1 := hN1 (max N1 N2 + 1) (by omega)
  have h2 := hN2 (max N1 N2 + 1) (by omega)
  have key : |L - M| ≤ |a (max N1 N2 + 1) - L| + |a (max N1 N2 + 1) - M| := by
    calc |L - M|
        = |(L - a (max N1 N2 + 1)) + (a (max N1 N2 + 1) - M)| := by ring_nf
      _ ≤ |L - a (max N1 N2 + 1)| + |a (max N1 N2 + 1) - M| := abs_add_le _ _
      _ = |a (max N1 N2 + 1) - L| + |a (max N1 N2 + 1) - M| := by
          rw [abs_sub_comm]
  linarith

/- ============================================================
   §Ch7  Limits of Functions (book §7.1)
   ============================================================ -/

def FuncLimit (f : Real -> Real) (a L : Real) : Prop :=
  forall eps : Real, eps > 0 ->
    exists delta : Real, delta > 0 /\
      forall x : Real, 0 < |x - a| -> |x - a| < delta -> |f x - L| < eps

-- Example: lim_{x -> 2} (x^2) = 4, with delta = min 1 (eps/5)
example : FuncLimit (fun x => x * x) 2 4 := by
  intro eps heps
  refine ⟨min 1 (eps / 5), by positivity, fun x _ hxd => ?_⟩
  have hx1 : |x - 2| < 1     := lt_of_lt_of_le hxd (min_le_left _ _)
  have hx5 : |x - 2| < eps/5 := lt_of_lt_of_le hxd (min_le_right _ _)
  have hbound : |x + 2| < 5 := by
    have h := abs_add_le (x - 2) 4
    have e : x - 2 + 4 = x + 2 := by ring
    rw [e] at h
    have h4 : |(4 : Real)| = 4 := by norm_num
    linarith
  calc |x * x - 4| = |x - 2| * |x + 2| := by rw [← abs_mul]; ring_nf
    _ < (eps / 5) * 5 := mul_lt_mul'' hx5 hbound (abs_nonneg _) (abs_nonneg _)
    _ = eps := by ring

/- ============================================================
   §Ch8  Continuity (book §8.1)
   ============================================================ -/

def ContinuousAt (f : Real -> Real) (a : Real) : Prop :=
  forall eps : Real, eps > 0 ->
    exists delta : Real, delta > 0 /\
      forall x : Real, |x - a| < delta -> |f x - f a| < eps

-- Polynomials are continuous: x^2 is continuous at every a
theorem sq_continuous_at (a : Real) : ContinuousAt (fun x => x * x) a := by
  intro eps heps
  -- |x^2 - a^2| = |x-a||x+a|. If |x-a| < 1, |x+a| <= |x-a| + 2|a| < 1 + 2|a|
  refine ⟨min 1 (eps / (2 * |a| + 2)), by positivity, fun x hx => ?_⟩
  have hd1 : |x - a| < 1 := lt_of_lt_of_le hx (min_le_left _ _)
  have hde : |x - a| < eps / (2 * |a| + 2) :=
    lt_of_lt_of_le hx (min_le_right _ _)
  have hxa : |x + a| < 2 * |a| + 1 := by
    have h : |x + a| <= |x - a| + 2 * |a| := by
      calc |x + a| = |(x - a) + 2 * a| := by ring_nf
        _ <= |x - a| + |2 * a| := abs_add_le _ _
        _ = |x - a| + 2 * |a| := by rw [abs_mul]; norm_num
    linarith
  calc |x * x - a * a|
      = |x - a| * |x + a| := by rw [← abs_mul]; ring_nf
    _ < (eps / (2 * |a| + 2)) * (2 * |a| + 2) :=
        mul_lt_mul'' hde (by linarith) (abs_nonneg _) (abs_nonneg _)
    _ = eps := div_mul_cancel₀ eps (by positivity)

/- ============================================================
   §Ch10  The Derivative (book §10.1)
   ============================================================ -/

def HasDerivAt (f : Real -> Real) (x L : Real) : Prop :=
  forall eps : Real, eps > 0 ->
    exists delta : Real, delta > 0 /\
      forall h : Real, |h| < delta -> h ≠ 0 ->
        |(f (x + h) - f x) / h - L| < eps

-- The derivative of a constant is zero
theorem const_deriv (c x : Real) : HasDerivAt (fun _ => c) x 0 := by
  intro eps heps
  refine ⟨1, one_pos, fun h _ _ => ?_⟩
  simpa using heps

-- The derivative of x is 1
theorem id_deriv (x : Real) : HasDerivAt id x 1 := by
  intro eps heps
  refine ⟨1, one_pos, fun h _ hne => ?_⟩
  simpa [div_self hne] using heps

-- Differentiability implies continuity
-- BOOK'S OWN SORRY: the full proof is left as an exercise
theorem differentiable_implies_continuous (f : Real -> Real) (x L : Real)
    (hf : HasDerivAt f x L) : ContinuousAt f x := by
  sorry -- full proof uses: f(x+h) - f(x) = h * ((f(x+h)-f(x))/h) -> 0

/- ============================================================
   §Ch11  Differentiation Rules (book §11.1)
   Both theorems are stated and left `sorry` BY THE BOOK.
   ============================================================ -/

theorem product_rule (f g : Real -> Real) (x Lf Lg : Real)
    (hf : HasDerivAt f x Lf) (hg : HasDerivAt g x Lg) :
    HasDerivAt (fun x => f x * g x) x (Lf * g x + f x * Lg) := by
  sorry  -- BOOK'S OWN SORRY: "Full proof requires bounding g near x"

theorem chain_rule (f g : Real -> Real) (x Lf Lg : Real)
    (hg : HasDerivAt g x Lg) (hf : HasDerivAt f (g x) Lf) :
    HasDerivAt (f ∘ g) x (Lf * Lg) := by
  sorry  -- BOOK'S OWN SORRY: "Requires the local linearity formulation"

/- ============================================================
   §Ch15  The Riemann Integral (book §15.1) — sketch, book's own
   sorries for the sup/inf on subintervals.
   ============================================================ -/

-- A partition of [a, b]
structure Partition (a b : Real) where
  points : List Real
  sorted : points.Pairwise (· ≤ ·)
  starts : points.head? = some a
  ends   : points.getLast? = some b

-- Subintervals from a partition
def subintervals {a b : Real} (P : Partition a b) : List (Real × Real) :=
  P.points.zip P.points.tail

-- Upper and lower Darboux sums (sketch); f must be bounded for the
-- sup/inf on each subinterval to exist.
noncomputable def upperSum {a b : Real} (f : Real -> Real)
    (P : Partition a b) : Real :=
  (subintervals P).foldl (fun acc (p : Real × Real) =>
    let Mi : Real := sorry  -- sup of f on [p.1, p.2]  (BOOK'S OWN SORRY)
    acc + Mi * (p.2 - p.1)) 0

noncomputable def lowerSum {a b : Real} (f : Real -> Real)
    (P : Partition a b) : Real :=
  (subintervals P).foldl (fun acc (p : Real × Real) =>
    let mi : Real := sorry  -- inf of f on [p.1, p.2]  (BOOK'S OWN SORRY)
    acc + mi * (p.2 - p.1)) 0

-- Riemann integrability (for bounded f)
def IsIntegrable (f : Real -> Real) (a b : Real) : Prop :=
  exists I : Real,
    forall eps : Real, eps > 0 ->
      exists P : Partition a b,
        upperSum f P - I < eps /\ I - lowerSum f P < eps

/- ============================================================
   §Ch16  FTC Part 2 (book §16.2) — honest Mathlib reformulation:
   stated against Mathlib's own HasDerivAt (written
   _root_.HasDerivAt to distinguish it from the book's
   epsilon–delta version) and its interval integral, and PROVED by
   Mathlib's intervalIntegral.integral_eq_sub_of_hasDerivAt.
   ============================================================ -/

theorem ftc_part2 (f G : Real -> Real) (a b : Real)
    (hderiv : ∀ x ∈ Set.uIcc a b, _root_.HasDerivAt G (f x) x)
    (hint : IntervalIntegrable f MeasureTheory.volume a b) :
    ∫ x in a..b, f x = G b - G a :=
  intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint

/- ============================================================
   §Ch21  Taylor Series for exp (book Ch. 21 leanbox)
   The two theorems are stated and left `sorry` BY THE BOOK.
   ============================================================ -/

-- Taylor polynomials for e^x
noncomputable def expTaylor (n : Nat) (x : Real) : Real :=
  Finset.sum (Finset.range (n + 1)) (fun k =>
    x ^ k / (Nat.factorial k : Real))

-- The k-th term
noncomputable def expTerm (k : Nat) (x : Real) : Real :=
  x ^ k / (Nat.factorial k : Real)

-- Ratio test: |a_{k+1}/a_k| = |x|/(k+1) -> 0 for any fixed x
theorem expTaylor_converges (x : Real) :
    SeqLimit (fun n => expTaylor n x) (Real.exp x) := by
  sorry  -- BOOK'S OWN SORRY: requires series convergence machinery

-- e^x satisfies (e^x)' = e^x
theorem exp_deriv (x : Real) : HasDerivAt Real.exp x (Real.exp x) := by
  sorry  -- BOOK'S OWN SORRY: term-by-term differentiation

/- ============================================================
   §Ch22  R^n (book §22.1) — Cauchy–Schwarz is the book's own sorry
   ============================================================ -/

def Vec (n : Nat) := Fin n -> Real

def dotProduct {n : Nat} (v w : Vec n) : Real :=
  Finset.sum Finset.univ (fun i => v i * w i)

def normSq {n : Nat} (v : Vec n) : Real :=
  dotProduct v v

noncomputable def euclidNorm {n : Nat} (v : Vec n) : Real :=
  Real.sqrt (normSq v)

-- Cauchy-Schwarz
theorem cauchy_schwarz {n : Nat} (v w : Vec n) :
    dotProduct v w ^ 2 <= normSq v * normSq w := by
  -- Classic proof via discriminant
  have h : forall t : Real,
      0 <= normSq (fun i => v i + t * w i) := fun t => by
    unfold normSq dotProduct
    exact Finset.sum_nonneg fun i _ => mul_self_nonneg _
  -- The LHS is a non-negative quadratic in t: ||v||^2 + 2t(v.w) + t^2||w||^2
  -- Discriminant must be <= 0
  sorry  -- BOOK'S OWN SORRY

/- ============================================================
   §Ch23  Partial derivatives (book §23.1) — the book's original
   sketch was ill-typed; fixed with Mathlib's deriv.
   ============================================================ -/

-- Partial derivative: fix all coordinates except the i-th and take
-- Mathlib's one-variable derivative of the resulting function.
noncomputable def partialDeriv {n : Nat} (f : Vec n -> Real)
    (i : Fin n) (a : Vec n) : Real :=
  deriv (fun t => f (Function.update a i t)) (a i)

-- Total (Frechet) derivative as a linear map
def HasTotalDerivAt {n : Nat} (f : Vec n -> Real) (a : Vec n)
    (L : Vec n -> Real) : Prop :=
  (forall v w : Vec n, L (fun i => v i + w i) = L v + L w) /\
  (forall c : Real, forall v, L (fun i => c * v i) = c * L v) /\
  forall eps : Real, eps > 0 ->
    exists delta : Real, delta > 0 /\
      forall h : Vec n, euclidNorm h < delta -> euclidNorm h > 0 ->
        |f (fun i => a i + h i) - f a - L h| < eps * euclidNorm h

end VCM

/- ============================================================
   §Ch36  Correctness of diff — the honest version.

   The Expr type, simplifier and diff engine are copied verbatim
   from the (core-Lean-verified) capstone code in
   CalculusVerification.lean. We then give a REAL-valued semantics
   Expr.evalR and prove the correctness lemmas the book prints:
   the Const and Var cases of diff itself, plus the rule-level
   lemmas for Add and Sin. The remaining cases are the book's
   declared extended exercise; the book's prose explains why the
   statement for the shipped `diff` (which constant-folds in Float
   inside fullSimplify) cannot hold exactly over ℝ.

   This namespace is top-level so that `HasDerivAt` below means
   MATHLIB's, as it would in the reader's capstone project.
   ============================================================ -/
namespace VCM36
set_option linter.unusedVariables false

inductive Expr where
  | Const  : Float -> Expr
  | Var    : String -> Expr
  | Add    : Expr -> Expr -> Expr
  | Sub    : Expr -> Expr -> Expr
  | Mul    : Expr -> Expr -> Expr
  | Div    : Expr -> Expr -> Expr
  | Pow    : Expr -> Expr -> Expr
  | Neg    : Expr -> Expr
  | Sin    : Expr -> Expr
  | Cos    : Expr -> Expr
  | Tan    : Expr -> Expr
  | Exp    : Expr -> Expr
  | Ln     : Expr -> Expr
  | Abs    : Expr -> Expr
  deriving Repr, BEq

open Expr

def Expr.simplify : Expr -> Expr
  | Add (Const a) (Const b)  => Const (a + b)
  | Sub (Const a) (Const b)  => Const (a - b)
  | Mul (Const a) (Const b)  => Const (a * b)
  | Div (Const a) (Const b)  =>
      if b != 0 then Const (a / b) else Div (Const a) (Const b)
  | Add e (Const c)          =>
      if c == 0 then e.simplify else Add e.simplify (Const c)
  | Add (Const c) e          =>
      if c == 0 then e.simplify else Add (Const c) e.simplify
  | Mul e (Const c)          =>
      if c == 1 then e.simplify
      else if c == 0 then Const 0
      else Mul e.simplify (Const c)
  | Mul (Const c) e          =>
      if c == 1 then e.simplify
      else if c == 0 then Const 0
      else Mul (Const c) e.simplify
  | Pow e (Const c)          =>
      if c == 1 then e.simplify
      else if c == 0 then Const 1
      else if e == Const 1 then Const 1
      else Pow e.simplify (Const c)
  | Pow (Const c) e          =>
      if c == 1 then Const 1 else Pow (Const c) e.simplify
  | Neg (Neg e)              => e.simplify
  | Add e1 e2                => Add e1.simplify e2.simplify
  | Sub e1 e2                => Sub e1.simplify e2.simplify
  | Mul e1 e2                => Mul e1.simplify e2.simplify
  | Div e1 e2                => Div e1.simplify e2.simplify
  | Pow e1 e2                => Pow e1.simplify e2.simplify
  | Neg e                    => Neg e.simplify
  | Sin e                    => Sin e.simplify
  | Cos e                    => Cos e.simplify
  | Tan e                    => Tan e.simplify
  | Exp e                    => Exp e.simplify
  | Ln  e                    => Ln  e.simplify
  | Abs e                    => Abs e.simplify
  | e                        => e

def Expr.fullSimplify (e : Expr) (fuel : Nat := 20) : Expr :=
  match fuel with
  | 0     => e
  | n + 1 =>
    let e' := e.simplify
    if e' == e then e else e'.fullSimplify n

inductive DiffStep where
  | ConstRule   : DiffStep
  | VarRule     : DiffStep
  | VarOther    : DiffStep
  | SumRule     : DiffStep -> DiffStep -> DiffStep
  | SubRule     : DiffStep -> DiffStep -> DiffStep
  | ProductRule : DiffStep -> DiffStep -> DiffStep
  | QuotRule    : DiffStep -> DiffStep -> DiffStep
  | ChainRule   : String   -> DiffStep -> DiffStep
  | PowerRule   : DiffStep
  | NegRule     : DiffStep -> DiffStep
  deriving Repr

def diff (x : String) : Expr -> Expr × DiffStep
  | .Const _     => (Const 0, .ConstRule)
  | .Var y       => if y == x
                   then (Const 1, .VarRule)
                   else (Const 0, .VarOther)
  | .Neg u       =>
      let (u', s) := diff x u
      (Neg u', .NegRule s)
  | .Add u v     =>
      let (u', su) := diff x u
      let (v', sv) := diff x v
      (Add u' v' |>.fullSimplify, .SumRule su sv)
  | .Sub u v     =>
      let (u', su) := diff x u
      let (v', sv) := diff x v
      (Sub u' v' |>.fullSimplify, .SubRule su sv)
  | .Mul u v     =>
      let (u', su) := diff x u
      let (v', sv) := diff x v
      ((Add (Mul u' v) (Mul u v')).fullSimplify, .ProductRule su sv)
  | .Div u v     =>
      let (u', su) := diff x u
      let (v', sv) := diff x v
      ((Div (Sub (Mul u' v) (Mul u v')) (Pow v (Const 2))).fullSimplify,
       .QuotRule su sv)
  | .Pow u (Const n) =>
      let (u', su) := diff x u
      ((Mul (Mul (Const n) (Pow u (Const (n-1)))) u').fullSimplify,
       .PowerRule)
  | .Sin u       =>
      let (u', su) := diff x u
      ((Mul (Cos u) u').fullSimplify, .ChainRule "sin" su)
  | .Cos u       =>
      let (u', su) := diff x u
      ((Neg (Mul (Sin u) u')).fullSimplify, .ChainRule "cos" su)
  | .Tan u       =>
      let (u', su) := diff x u
      ((Div u' (Pow (Cos u) (Const 2))).fullSimplify, .ChainRule "tan" su)
  | .Exp u       =>
      let (u', su) := diff x u
      ((Mul (Exp u) u').fullSimplify, .ChainRule "exp" su)
  | .Ln u        =>
      let (u', su) := diff x u
      ((Div u' u).fullSimplify, .ChainRule "ln" su)
  | .Pow u v     =>
      let (u', su) := diff x u
      let (v', sv) := diff x v
      let result := Mul (Pow u v)
                        (Add (Mul v' (Ln u)) (Div (Mul v u') u))
      (result.fullSimplify, .ChainRule "pow" (.ProductRule su sv))
  | .Abs _       => (Const 0, .ConstRule)

-- ================= BOOK LISTING (Ch. 36) begins =================

-- A real-valued semantics for Expr: interpret e as a function of
-- the single variable x. The Float constants stored in the tree
-- are read through a map ι : Float → ℝ (think: "the exact rational
-- value this Float denotes"); we only ever require ι 0 = 0 and
-- ι 1 = 1.
noncomputable def Expr.evalR (ι : Float -> Real) (x : String) :
    Expr -> Real -> Real
  | .Const c   => fun _ => ι c
  | .Var y     => fun t => if y == x then t else 0
  | .Add u v   => fun t => u.evalR ι x t + v.evalR ι x t
  | .Sub u v   => fun t => u.evalR ι x t - v.evalR ι x t
  | .Mul u v   => fun t => u.evalR ι x t * v.evalR ι x t
  | .Div u v   => fun t => u.evalR ι x t / v.evalR ι x t
  | .Pow u v   => fun t => u.evalR ι x t ^ v.evalR ι x t   -- Real.rpow
  | .Neg u     => fun t => -(u.evalR ι x t)
  | .Sin u     => fun t => Real.sin (u.evalR ι x t)
  | .Cos u     => fun t => Real.cos (u.evalR ι x t)
  | .Tan u     => fun t => Real.tan (u.evalR ι x t)
  | .Exp u     => fun t => Real.exp (u.evalR ι x t)
  | .Ln  u     => fun t => Real.log (u.evalR ι x t)
  | .Abs u     => fun t => |u.evalR ι x t|

-- Base case: constants differentiate to 0.
theorem diff_correct_const (ι : Float -> Real) (hι0 : ι 0 = 0)
    (x : String) (c : Float) (t : Real) :
    HasDerivAt ((Expr.Const c).evalR ι x)
      (((diff x (.Const c)).1).evalR ι x t) t := by
  simpa [diff, Expr.evalR, hι0] using hasDerivAt_const t (ι c)

-- Base case: the variable differentiates to 1, other variables to 0.
theorem diff_correct_var (ι : Float -> Real) (hι0 : ι 0 = 0)
    (hι1 : ι 1 = 1) (x y : String) (t : Real) :
    HasDerivAt ((Expr.Var y).evalR ι x)
      (((diff x (.Var y)).1).evalR ι x t) t := by
  by_cases h : y == x
  · simpa [diff, h, Expr.evalR, hι1] using hasDerivAt_id' t
  · simpa [diff, h, Expr.evalR, hι0] using hasDerivAt_const t (0 : Real)

-- Inductive step for Add: the SUM RULE of Chapter 11, at the level
-- of expression trees. (This is the rule diff's Add case applies,
-- before its final simplification pass.)
theorem add_rule_correct (ι : Float -> Real) (x : String)
    {u v u' v' : Expr} {t : Real}
    (hu : HasDerivAt (u.evalR ι x) (u'.evalR ι x t) t)
    (hv : HasDerivAt (v.evalR ι x) (v'.evalR ι x t) t) :
    HasDerivAt ((Expr.Add u v).evalR ι x)
      ((Expr.Add u' v').evalR ι x t) t :=
  hu.add hv

-- Inductive step for Sin: the CHAIN RULE, ditto.
theorem sin_rule_correct (ι : Float -> Real) (x : String)
    {u u' : Expr} {t : Real}
    (hu : HasDerivAt (u.evalR ι x) (u'.evalR ι x t) t) :
    HasDerivAt ((Expr.Sin u).evalR ι x)
      ((Expr.Mul (Expr.Cos u) u').evalR ι x t) t := by
  simpa [Expr.evalR] using hu.sin

-- ================== BOOK LISTING (Ch. 36) ends ==================

end VCM36

/- ============================================================
   §Primer — Appendix A "A Lean 4 Primer": every Mathlib-tactic
   example printed in the appendix, compiled. (The core-Lean
   examples of the appendix are compiled in
   CalculusVerification.lean, namespace PrimerAppendix.)
   ============================================================ -/
namespace VCMPrimer

-- linarith: closes goals that follow from the hypotheses by LINEAR
-- arithmetic over an ordered field.
example (x y : Real) (h1 : x < 2 * y) (h2 : y ≤ 3) : x < 6 := by
  linarith

-- nlinarith: linarith plus some NONLINEAR preprocessing (products
-- of hypotheses, squares); hints can be passed in brackets.
example (a : Real) : 0 ≤ a ^ 2 - 2 * a + 1 := by
  nlinarith [sq_nonneg (a - 1)]

-- norm_num: evaluates numeric goals.
example : (2 : Real) + 2 ≠ 5 := by norm_num
example : (127 : Nat).Prime := by norm_num

-- positivity: proves goals of the form 0 < e, 0 ≤ e, or e ≠ 0.
example (x : Real) (hx : 0 < x) : 0 < x ^ 2 / (x + 1) := by positivity

-- push_neg: pushes negations through quantifiers and connectives.
example (P : Nat -> Prop) (h : ¬ ∀ n, P n) : ∃ n, ¬ P n := by
  push_neg at h
  exact h

-- by_contra: proof by contradiction...
example (x : Real) (h : ∀ eps : Real, eps > 0 -> x ≤ eps) : x ≤ 0 := by
  by_contra hx
  push_neg at hx
  have := h (x / 2) (by linarith)
  linarith

-- ...which is sugar for Classical.byContradiction:
example (p : Prop) (h : ¬¬p) : p :=
  Classical.byContradiction fun hnp => h hnp

-- ring: proves identities that hold in every commutative ring.
example (a b : Real) : (a + b) ^ 2 = a ^ 2 + 2 * a * b + b ^ 2 := by ring

-- set: names a subexpression and replaces it everywhere.
example (a b : Real) (h : a + b > 2) : (a + b) ^ 2 > 4 := by
  set s := a + b with hs
  nlinarith

-- field_simp: clears denominators (given proofs they are nonzero).
example (x : Real) (hx : x ≠ 0) : 1 / x + 1 = (1 + x) / x := by
  field_simp

end VCMPrimer
