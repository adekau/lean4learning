/- ============================================================
   Verified Calculus — companion verification file
   From the Natural Numbers to Symbolic Solvers in Lean 4

   Verification of the Lean 4 code printed in
   calculus/verified-calculus-complete.tex, checked against a
   plain-core toolchain (leanprover/lean4:v4.28.0, NO Mathlib —
   which is what the book itself claims to use: "No Mathlib. No
   shortcuts.").

   Layout (namespaces track book chapters):
     VC.Ch1   — The Natural Numbers (MyNat)
     VC.Ch2   — The Integers (IntRel, MyInt)
     VC.Ch3   — The Rationals (MyRat)
     VC.Ch4   — Irrationality of sqrt 2
     VC.Ch5   — The Reals (Cauchy sequences, MyReal)
     VC.Ch6   — Sequences (SeqLimit, uniqueness)
     VC.Ch7   — Limits of functions (FuncLimit, x^2 -> 4)
     VC.Ch8   — Continuity (ContinuousAt, x^2 continuous)
     VC.Ch10  — The derivative (HasDerivAt, const/id rules)
     VC.Ch11  — Differentiation rules (book leaves sorries)
     VC.Ch14  — Newton's method
     VC.Ch15  — Riemann integral sketch (book leaves sorries)
     VC.Ch16  — FTC (book leaves sorry)
     VC.Ch21  — Taylor series for exp (book leaves sorries)
     VC.Ch22  — R^n (book leaves sorry; Ch. 23 notes included)
     Symboliculus — Part VII capstone (Chs. 31–35)

   IMPORTANT GLOBAL DEVIATION: the book's analysis code (Ch. 6
   onward) is written against Mathlib's `Real` type, `|·|` abs
   notation, `Finset`, and Mathlib tactics (linarith, nlinarith,
   positivity, norm_num, ring_nf, push_neg, by_contra, set,
   Nat.Coprime API beyond core, List.Sorted, deriv, Real.exp,
   Real.sqrt, Real.sin ...). NONE of these exist in the no-Mathlib
   toolchain the book describes. Every such snippet fails with
   "unknown identifier 'Real'" / "unknown tactic" as printed.
   Here they are ported to `Rat` (the statements proved are
   ordered-field facts, so they are faithful) with a hand-rolled
   `rabs`, and Mathlib tactics replaced by core `grind`/`omega`
   or manual lemmas. Each local deviation is marked "DEVIATION".

   `sorry` appears ONLY where the book itself prints `sorry`
   (Chs. 10, 11, 15, 16, 21, 22, 31, 33); each is marked.
   ============================================================ -/

namespace VC

/- ============================================================
   §Ch1  The Natural Numbers (book §1.1–1.3)
   ============================================================ -/
namespace Ch1

-- Book Ch. 1, "The Peano Axioms" leanbox: verbatim, compiles.
inductive MyNat : Type where
  | zero : MyNat
  | succ : MyNat -> MyNat
  deriving Repr

def MyNat.one   : MyNat := MyNat.succ MyNat.zero
def MyNat.two   : MyNat := MyNat.succ MyNat.one
def MyNat.three : MyNat := MyNat.succ MyNat.two

theorem mynat_ind (P : MyNat -> Prop)
    (h0 : P MyNat.zero)
    (hs : forall n, P n -> P (MyNat.succ n)) :
    forall n, P n := fun n => by
  induction n with
  | zero      => exact h0
  | succ n ih => exact hs n ih

-- Book Ch. 1, "Arithmetic by Recursion" leanbox: verbatim, compiles.
@[simp] def MyNat.add : MyNat -> MyNat -> MyNat
  | n, .zero   => n
  | n, .succ m => .succ (n.add m)

@[simp] def MyNat.mul : MyNat -> MyNat -> MyNat
  | _, .zero   => .zero
  | n, .succ m => (n.mul m).add n

instance : Add MyNat := ⟨MyNat.add⟩
instance : Mul MyNat := ⟨MyNat.mul⟩

@[simp] theorem MyNat.add_def (m n : MyNat) : m + n = m.add n := rfl
@[simp] theorem MyNat.mul_def (m n : MyNat) : m * n = m.mul n := rfl

theorem MyNat.zero_add (n : MyNat) : MyNat.zero.add n = n := by
  induction n with
  | zero      => rfl
  | succ n ih => simp [ih]

theorem MyNat.succ_add (n m : MyNat) : n.succ.add m = (n.add m).succ := by
  induction m with
  | zero      => rfl
  | succ m ih => simp [ih]

theorem MyNat.add_comm (m n : MyNat) : m.add n = n.add m := by
  induction n with
  | zero      => simp [MyNat.zero_add]
  | succ n ih => simp [MyNat.succ_add, ih]

theorem MyNat.add_assoc (a b c : MyNat) : (a.add b).add c = a.add (b.add c) := by
  induction c with
  | zero      => rfl
  | succ c ih => simp [ih]

/- DEVIATION (book Ch. 1, "Order on N" leanbox). The book's code
   uses `k < n`, `k <= n`, `le_refl` on MyNat but NEVER defines an
   LE/LT instance or any order lemmas — as printed it fails with
   "failed to synthesize LE MyNat / LT MyNat" and
   "unknown identifier 'le_refl'". Worse, its `strong_ind` proof
   applies *Nat* lemmas (Nat.le_zero, Nat.not_lt_zero,
   Nat.lt_or_eq_of_le, Nat.lt_succ_iff) to MyNat hypotheses:
   type errors. We supply the missing order instances and the
   MyNat-specific helper lemmas (cf. the working development in
   calculus/Calculus.lean). -/

def MyNat.le (m n : MyNat) : Prop := ∃ k : MyNat, m.add k = n
def MyNat.lt (m n : MyNat) : Prop := m.le n ∧ m ≠ n

instance : LE MyNat := ⟨MyNat.le⟩
instance : LT MyNat := ⟨MyNat.lt⟩

theorem MyNat.le_refl (n : MyNat) : n ≤ n := ⟨.zero, rfl⟩

-- Book "no_overflow": DEVIATION — the book's succ case
-- `simp [MyNat.add]; exact ih` fails ("type mismatch: ih has type
-- n.add m.succ ≠ n but is expected to have type ¬n.succ.add m = n");
-- the rewrite needs succ_add, which we add to the simp set.
theorem MyNat.no_overflow (n m : MyNat) : n.add m.succ ≠ n := by
  induction n with
  | zero      => simp [MyNat.add]
  | succ n ih => simp [MyNat.add, MyNat.succ_add] at *; exact ih

-- Book "add_eq_self": verbatim, compiles (given fixed no_overflow).
theorem MyNat.add_eq_self (n k : MyNat) : n.add k = n -> k = .zero := by
  cases k with
  | zero   => intros; rfl
  | succ k => intro h; exact absurd h (MyNat.no_overflow n k)

-- Book "add_eq_zero_left": verbatim, compiles.
theorem MyNat.add_eq_zero_left {a b : MyNat}
    (h : a.add b = .zero) : a = .zero := by
  cases a with
  | zero   => rfl
  | succ a => cases b <;> simp [MyNat.add] at h

-- Book "le_antisymm": compiles verbatim once the LE instance exists.
theorem MyNat.le_antisymm {n m : MyNat}
    (h1 : n <= m) (h2 : m <= n) : n = m := by
  obtain ⟨k, hk⟩ := h1
  obtain ⟨j, hj⟩ := h2
  have hkj : n.add (k.add j) = n := by
    calc n.add (k.add j)
        = (n.add k).add j := (MyNat.add_assoc n k j).symm
      _ = m.add j         := by rw [show n.add k = m from hk]
      _ = n               := hj
  have h0 : k.add j = .zero := MyNat.add_eq_self n _ hkj
  have hk0 : k = .zero     := MyNat.add_eq_zero_left h0
  simp [hk0, MyNat.add] at hk
  exact hk

-- Helper lemmas the book's strong_ind/well_ordering silently assume
-- (DEVIATION: absent from the book; Nat.* analogues do not apply).
theorem MyNat.le_zero_mp {n : MyNat} (h : n ≤ .zero) : n = .zero := by
  obtain ⟨k, hk⟩ := h
  exact MyNat.add_eq_zero_left hk

theorem MyNat.not_lt_zero (n : MyNat) : ¬ n < .zero := by
  intro ⟨hle, hne⟩
  exact hne (MyNat.le_zero_mp hle)

theorem MyNat.lt_or_eq_of_le {n m : MyNat} (h : n ≤ m) : n < m ∨ n = m := by
  obtain ⟨k, hk⟩ := h
  cases k with
  | zero   => exact Or.inr (by simpa [MyNat.add] using hk)
  | succ k =>
    refine Or.inl ⟨⟨k.succ, hk⟩, ?_⟩
    intro heq
    subst heq
    exact MyNat.no_overflow n k hk

theorem MyNat.lt_succ_mp {n m : MyNat} (h : n < m.succ) : n ≤ m := by
  obtain ⟨⟨k, hk⟩, hne⟩ := h
  cases k with
  | zero   => exact absurd (by simpa [MyNat.add] using hk) hne
  | succ k =>
    exact ⟨k, by simpa [MyNat.add] using hk⟩

theorem MyNat.le_succ_of_le {n m : MyNat} (h : n ≤ m) : n ≤ m.succ := by
  obtain ⟨k, hk⟩ := h
  exact ⟨k.succ, by simp [MyNat.add, hk]⟩

-- Book "strong_ind": DEVIATION — proof rewritten with the MyNat
-- lemmas above (the printed proof used Nat lemmas on MyNat and an
-- undefined order; it does not typecheck).
theorem MyNat.strong_ind (P : MyNat -> Prop)
    (step : forall n, (forall k, k < n -> P k) -> P n) :
    forall n, P n := by
  suffices h : forall n, forall k, k <= n -> P k from
    fun n => h n n (MyNat.le_refl n)
  intro n
  induction n with
  | zero =>
    intro k hk
    have hkz : k = MyNat.zero := MyNat.le_zero_mp hk
    subst hkz
    exact step .zero (fun k hlt => absurd hlt (MyNat.not_lt_zero k))
  | succ n ih =>
    intro k hk
    rcases MyNat.lt_or_eq_of_le hk with hlt | rfl
    · exact ih k (MyNat.lt_succ_mp hlt)
    · exact step (.succ n) (fun j hj => ih j (MyNat.lt_succ_mp hj))

theorem MyNat.succ_ne_self (n : MyNat) : n.succ ≠ n := by
  induction n with
  | zero      => simp
  | succ n ih => intro h; exact ih (MyNat.succ.inj h)

theorem MyNat.le_succ_self (n : MyNat) : n ≤ n.succ := ⟨.one, rfl⟩

theorem MyNat.lt_succ_self (n : MyNat) : n < n.succ :=
  ⟨MyNat.le_succ_self n, fun h => MyNat.succ_ne_self n h.symm⟩

theorem MyNat.succ_le_of_lt {n m : MyNat} (h : n < m) : n.succ ≤ m := by
  obtain ⟨⟨k, hk⟩, hne⟩ := h
  cases k with
  | zero   => exact absurd (by simpa [MyNat.add] using hk) hne
  | succ k => exact ⟨k, by subst hk; simp [MyNat.add, MyNat.succ_add]⟩

theorem MyNat.lt_succ_of_lt {n m : MyNat} (h : n < m) : n < m.succ := by
  obtain ⟨⟨k, hk⟩, _⟩ := h
  constructor
  · exact ⟨k.succ, by simp [MyNat.add, hk]⟩
  · intro heq
    subst heq
    exact MyNat.no_overflow m k
      (by simpa [MyNat.add, MyNat.succ_add] using hk)

theorem MyNat.lt_or_ge (n m : MyNat) : n < m ∨ m ≤ n := by
  induction m with
  | zero      => exact Or.inr ⟨n, MyNat.zero_add n⟩
  | succ m ih =>
    rcases ih with hlt | hge
    · exact Or.inl (MyNat.lt_succ_of_lt hlt)
    · rcases MyNat.lt_or_eq_of_le hge with hlt | rfl
      · exact Or.inr (MyNat.succ_le_of_lt hlt)
      · exact Or.inl (MyNat.lt_succ_self _)

theorem MyNat.lt_of_not_le {a b : MyNat} (hn : ¬ a ≤ b) : b < a :=
  (MyNat.lt_or_ge b a).resolve_right hn

-- Book "well_ordering": DEVIATION — the printed proof is
-- structurally broken: after `by_contra`/`push_neg` (push_neg is a
-- Mathlib tactic; by_contra is also unavailable in this core
-- toolchain) the goal is False, to which `apply MyNat.strong_ind`
-- cannot apply. Rewritten via strong induction + Classical.em
-- (cf. Calculus.lean).
theorem MyNat.well_ordering (S : MyNat -> Prop) (hne : ∃ n, S n) :
    ∃ m, S m ∧ ∀ k, S k -> m ≤ k := by
  obtain ⟨n, hn⟩ := hne
  refine MyNat.strong_ind (fun n => S n → ∃ m, S m ∧ ∀ k, S k → m ≤ k) ?_ n hn
  intro n ih hSn
  rcases Classical.em (∀ k, S k → n ≤ k) with hmin | hnotmin
  · exact ⟨n, hSn, hmin⟩
  · rw [Classical.not_forall] at hnotmin
    obtain ⟨k, hk⟩ := hnotmin
    rw [Classical.not_imp] at hk
    obtain ⟨hSk, hkn⟩ := hk
    exact ih k (MyNat.lt_of_not_le hkn) hSk

end Ch1

/- ============================================================
   §Ch2  The Integers (book §2.1)
   Book code compiles VERBATIM (it wisely switches to core Nat,
   so omega applies).
   ============================================================ -/
namespace Ch2

def IntRel : (Nat × Nat) -> (Nat × Nat) -> Prop
  | (a, b), (c, d) => a + d = b + c

theorem IntRel.refl : forall p : Nat × Nat, IntRel p p
  | (a, b) => by simp [IntRel, Nat.add_comm]

theorem IntRel.symm : forall p q, IntRel p q -> IntRel q p := by
  intro (a, b) (c, d) h; simp [IntRel] at *; omega

theorem IntRel.trans : forall p q r,
    IntRel p q -> IntRel q r -> IntRel p r := by
  intro (a, b) (c, d) (e, f) h1 h2
  simp [IntRel] at *
  omega

def MyInt : Type := Quot IntRel

def mkInt (a b : Nat) : MyInt := Quot.mk IntRel (a, b)

def intOfNat (n : Nat) : MyInt := mkInt n 0

def intZero : MyInt := mkInt 0 0
def intOne  : MyInt := mkInt 1 0

def intNeg (x : MyInt) : MyInt :=
  Quot.lift (fun p => mkInt p.2 p.1)
    (by intro (a, b) (c, d) h
        apply Quot.sound
        simp [IntRel] at *; omega) x

end Ch2

/- ============================================================
   §Ch3  The Rationals (book §3.1)
   Book code compiles verbatim EXCEPT `positivity` (a Mathlib
   tactic) in `midpoint`.
   ============================================================ -/
namespace Ch3

structure MyRat where
  num : Int
  den : Int
  den_pos : 0 < den

def ratEquiv (p q : MyRat) : Prop :=
  p.num * q.den = q.num * p.den

def addRat (p q : MyRat) : MyRat :=
  { num     := p.num * q.den + q.num * p.den,
    den     := p.den * q.den,
    den_pos := Int.mul_pos p.den_pos q.den_pos }

def mulRat (p q : MyRat) : MyRat :=
  { num     := p.num * q.num,
    den     := p.den * q.den,
    den_pos := Int.mul_pos p.den_pos q.den_pos }

def invRat (p : MyRat) (h : p.num ≠ 0) : MyRat :=
  if hp : 0 < p.num then
    { num := p.den, den := p.num, den_pos := hp }
  else
    { num := -p.den, den := -p.num,
      den_pos := by omega }

-- DEVIATION: book has `den_pos := by positivity` — unknown tactic
-- without Mathlib. Replaced with explicit Int.mul_pos steps.
def midpoint (p q : MyRat) : MyRat :=
  { num     := p.num * q.den + q.num * p.den,
    den     := 2 * p.den * q.den,
    den_pos := Int.mul_pos (Int.mul_pos (by omega) p.den_pos) q.den_pos }

end Ch3

/- ============================================================
   §Ch4  Irrationality of sqrt 2 (book §4.1)
   DEVIATION: the book's `even_of_sq_even` uses the nonexistent
   lemma `Nat.not_dvd_iff_odd` plus Mathlib tactics norm_num /
   linarith / by_contra; `sqrt2_irrational` uses linarith and
   norm_num. Proofs rewritten with core omega / gcd lemmas.
   Statements unchanged.
   ============================================================ -/
namespace Ch4

theorem even_of_sq_even (n : Nat) (h : 2 ∣ n * n) : 2 ∣ n := by
  rcases Nat.mod_two_eq_zero_or_one n with h0 | h1
  · exact Nat.dvd_of_mod_eq_zero h0
  · exfalso
    have h2 : (n * n) % 2 = 1 := by rw [Nat.mul_mod, h1]
    have h0 : (n * n) % 2 = 0 := Nat.mod_eq_zero_of_dvd h
    omega

theorem sqrt2_irrational :
    forall p q : Nat, q ≠ 0 -> Nat.Coprime p q -> p * p ≠ 2 * (q * q) := by
  intro p q hq hcop heq
  have h2p : 2 ∣ p := even_of_sq_even p ⟨q * q, heq⟩
  obtain ⟨k, rfl⟩ := h2p
  have hexp : 2 * k * (2 * k) = 2 * (2 * (k * k)) := by ac_rfl
  have heq' : 2 * (2 * (k * k)) = 2 * (q * q) := by rw [← hexp]; exact heq
  have hq2 : q * q = 2 * (k * k) := by omega
  have h2q : 2 ∣ q := even_of_sq_even q ⟨k * k, hq2⟩
  have hgcd : 2 ∣ Nat.gcd (2 * k) q := Nat.dvd_gcd ⟨k, rfl⟩ h2q
  rw [hcop] at hgcd
  omega

end Ch4

/- ============================================================
   Shared absolute-value machinery for Parts II–III.

   GLOBAL DEVIATION for every leanbox from Ch. 5 onward: the book
   writes `|x - y|` — but core Lean has NO `|·|` notation and no
   `abs` for Rat/Real (both are Mathlib). We define `rabs` and the
   handful of lemmas the book's proofs implicitly pull from Mathlib
   (abs_add, abs_mul, abs_nonneg, ...). Mathlib-only tactics
   (linarith, nlinarith, positivity, norm_num, ring_nf) are
   replaced by core `grind`/`omega` plus explicit lemmas.
   ============================================================ -/
namespace RatAbs

def rabs (q : Rat) : Rat := if q < 0 then -q else q

theorem rabs_nonneg (a : Rat) : 0 ≤ rabs a := by
  simp only [rabs]; grind

theorem rabs_zero : rabs 0 = 0 := by simp [rabs]

theorem rabs_pos_of_ne {a : Rat} (h : a ≠ 0) : 0 < rabs a := by
  simp only [rabs]; grind

theorem rabs_add (a b : Rat) : rabs (a + b) ≤ rabs a + rabs b := by
  simp only [rabs]; grind

theorem rabs_sub_comm (a b : Rat) : rabs (a - b) = rabs (b - a) := by
  simp only [rabs]; grind

theorem rabs_mul (a b : Rat) : rabs (a * b) = rabs a * rabs b := by
  have h1 : 0 ≤ a → 0 ≤ b → 0 ≤ a * b := fun ha hb => Rat.mul_nonneg ha hb
  have h2 : 0 ≤ a → 0 ≤ -b → 0 ≤ a * (-b) := fun ha hb => Rat.mul_nonneg ha hb
  have h3 : 0 ≤ -a → 0 ≤ b → 0 ≤ (-a) * b := fun ha hb => Rat.mul_nonneg ha hb
  have h4 : 0 ≤ -a → 0 ≤ -b → 0 ≤ (-a) * (-b) := fun ha hb => Rat.mul_nonneg ha hb
  have e1 : a * -b = -(a * b) := by grind
  have e2 : -a * b = -(a * b) := by grind
  have e3 : -a * -b = a * b := by grind
  simp only [rabs]; grind

/-- `a < b`, `c < d` with left factors nonnegative gives `a*c < b*d`. -/
theorem mul_lt_mul_of_nonneg {a b c d : Rat}
    (ha : 0 ≤ a) (hab : a < b) (hc : 0 ≤ c) (hcd : c < d) : a * c < b * d := by
  have h1 : 0 < (b - a) * d := Rat.mul_pos (by grind) (by grind)
  have h2 : 0 ≤ a * (d - c) := Rat.mul_nonneg ha (by grind)
  have key : b * d - a * c = (b - a) * d + a * (d - c) := by grind
  grind

theorem div_pos' {a b : Rat} (ha : 0 < a) (hb : 0 < b) : 0 < a / b := by
  have hinv : 0 < b⁻¹ := by
    by_cases h : 0 < b⁻¹
    · exact h
    · have h1 : 0 ≤ b * (-b⁻¹) := Rat.mul_nonneg (by grind) (by grind)
      have h2 : b * -b⁻¹ = -(b * b⁻¹) := by grind
      grind
  have := Rat.mul_pos ha hinv
  grind

end RatAbs

open RatAbs

/- ============================================================
   §Ch5  The Real Numbers (book §5.1)
   Book claim verified: `Rat` IS available in core Lean.
   DEVIATIONS: (a) `|·|` → rabs as above; (b) tactic proofs
   (`linarith`, `ring_nf`, `abs_add`) rewritten with grind/omega;
   (c) the book's `addReal` uses `Quot.lift2` — NO such constant
   exists in Lean 4 core (or Mathlib; Mathlib has Quotient.lift₂
   for Setoid quotients) — and supplies only ONE well-definedness
   proof where lifting a binary operation needs respect in BOTH
   arguments. Reimplemented with nested Quot.lift and both proofs.
   ============================================================ -/
namespace Ch5

def IsCauchy (a : Nat -> Rat) : Prop :=
  forall eps : Rat, eps > 0 ->
    exists N : Nat, forall m n : Nat, m > N -> n > N ->
      rabs (a m - a n) < eps

structure CauchySeq where
  seq    : Nat -> Rat
  cauchy : IsCauchy seq

def CauchyEquiv (a b : CauchySeq) : Prop :=
  forall eps : Rat, eps > 0 ->
    exists N : Nat, forall n : Nat, n > N ->
      rabs (a.seq n - b.seq n) < eps

def MyReal : Type := Quot CauchyEquiv

def ofRat (q : Rat) : MyReal :=
  Quot.mk CauchyEquiv
    { seq    := fun _ => q,
      cauchy := fun eps heps => ⟨0, fun _ _ _ _ => by
        have e : q - q = (0:Rat) := by grind
        rw [e, rabs_zero]; exact heps⟩ }

def addCauchy (a b : CauchySeq) : CauchySeq :=
  { seq    := fun n => a.seq n + b.seq n,
    cauchy := fun eps heps => by
      obtain ⟨Na, ha⟩ := a.cauchy (eps/2) (by grind)
      obtain ⟨Nb, hb⟩ := b.cauchy (eps/2) (by grind)
      refine ⟨max Na Nb, fun m n hm hn => ?_⟩
      have h1 := ha m n (by omega) (by omega)
      have h2 := hb m n (by omega) (by omega)
      have key : (a.seq m + b.seq m) - (a.seq n + b.seq n)
               = (a.seq m - a.seq n) + (b.seq m - b.seq n) := by grind
      have tri := rabs_add (a.seq m - a.seq n) (b.seq m - b.seq n)
      rw [key]; grind }

theorem addCauchy_respects_right (a b b' : CauchySeq)
    (h : CauchyEquiv b b') : CauchyEquiv (addCauchy a b) (addCauchy a b') := by
  intro eps heps
  obtain ⟨N, hN⟩ := h eps heps
  refine ⟨N, fun n hn => ?_⟩
  have hb := hN n hn
  show rabs ((a.seq n + b.seq n) - (a.seq n + b'.seq n)) < eps
  have key : (a.seq n + b.seq n) - (a.seq n + b'.seq n)
           = b.seq n - b'.seq n := by grind
  rw [key]; exact hb

theorem addCauchy_respects_left (a a' b : CauchySeq)
    (h : CauchyEquiv a a') : CauchyEquiv (addCauchy a b) (addCauchy a' b) := by
  intro eps heps
  obtain ⟨N, hN⟩ := h eps heps
  refine ⟨N, fun n hn => ?_⟩
  have ha := hN n hn
  show rabs ((a.seq n + b.seq n) - (a'.seq n + b.seq n)) < eps
  have key : (a.seq n + b.seq n) - (a'.seq n + b.seq n)
           = a.seq n - a'.seq n := by grind
  rw [key]; exact ha

def addReal : MyReal -> MyReal -> MyReal :=
  Quot.lift
    (fun a => Quot.lift (fun b => Quot.mk CauchyEquiv (addCauchy a b))
      (fun b b' h => Quot.sound (addCauchy_respects_right a b b' h)))
    (fun a a' h => by
      funext y
      induction y using Quot.ind with
      | mk b => exact Quot.sound (addCauchy_respects_left a a' b h))

end Ch5

/- ============================================================
   §Ch6  Sequences and Convergence (book §6.1)
   DEVIATION: the book's `Real` does not exist without Mathlib
   (error: unknown identifier 'Real'); ported to Rat. Statement
   and argument are ordered-field facts, unchanged in substance.
   The book's printed proof of `limit_unique` is additionally
   broken on its own terms: it contains `a _` placeholders inside
   a calc block (elaboration error even with Mathlib), a dead
   `have hn := max N1 N2 + 1`, and Mathlib-only tactics. Rewritten.
   ============================================================ -/
namespace Ch6

def SeqLimit (a : Nat -> Rat) (L : Rat) : Prop :=
  forall eps : Rat, eps > 0 ->
    exists N : Nat, forall n : Nat, n > N -> rabs (a n - L) < eps

theorem limit_unique (a : Nat -> Rat) (L M : Rat)
    (hL : SeqLimit a L) (hM : SeqLimit a M) : L = M := by
  refine Classical.byContradiction fun hne => ?_
  have hd : 0 < rabs (L - M) := rabs_pos_of_ne (fun h => hne (by grind))
  obtain ⟨N1, h1⟩ := hL (rabs (L - M) / 2) (by grind)
  obtain ⟨N2, h2⟩ := hM (rabs (L - M) / 2) (by grind)
  have hh1 := h1 (max N1 N2 + 1) (by omega)
  have hh2 := h2 (max N1 N2 + 1) (by omega)
  have tri := rabs_add (L - a (max N1 N2 + 1)) (a (max N1 N2 + 1) - M)
  have key : (L - a (max N1 N2 + 1)) + (a (max N1 N2 + 1) - M) = L - M := by
    grind
  have hsym : rabs (a (max N1 N2 + 1) - L)
            = rabs (L - a (max N1 N2 + 1)) := rabs_sub_comm _ _
  rw [key] at tri
  grind

end Ch6

/- ============================================================
   §Ch7  Limits of Functions (book §7.1)
   DEVIATION: Real → Rat as above; the worked example
   lim_{x→2} x² = 4 is re-proved with the SAME δ = min 1 (ε/5)
   and the same estimate |x²-4| = |x-2||x+2| < (ε/5)·5.
   (The book's own tactic script uses positivity/nlinarith/
   abs_lt/abs_le — all Mathlib.)
   ============================================================ -/
namespace Ch7

def FuncLimit (f : Rat -> Rat) (a L : Rat) : Prop :=
  forall eps : Rat, eps > 0 ->
    exists delta : Rat, delta > 0 /\
      forall x : Rat, 0 < rabs (x - a) -> rabs (x - a) < delta ->
        rabs (f x - L) < eps

example : FuncLimit (fun x => x * x) 2 4 := by
  intro eps heps
  have h5 : (0:Rat) < eps / 5 := div_pos' heps (by grind)
  refine ⟨min 1 (eps / 5), by grind, fun x _ hxd => ?_⟩
  have hx1 : rabs (x - 2) < 1     := by grind
  have hx5 : rabs (x - 2) < eps/5 := by grind
  have tri : rabs (x + 2) ≤ rabs (x - 2) + rabs 4 := by
    have h := rabs_add (x - 2) 4
    have e : (x - 2) + 4 = x + 2 := by grind
    rw [e] at h; exact h
  have h4 : rabs (4 : Rat) = 4 := by simp only [rabs]; grind
  have hbound : rabs (x + 2) < 5 := by grind
  have hfact : x * x - 4 = (x - 2) * (x + 2) := by grind
  show rabs (x * x - 4) < eps
  rw [hfact, rabs_mul]
  have hprod := mul_lt_mul_of_nonneg (rabs_nonneg (x - 2)) hx5
                  (rabs_nonneg (x + 2)) hbound
  have hcancel : eps / 5 * 5 = eps := by grind
  grind

end Ch7

/- ============================================================
   §Ch8  Continuity (book §8.1)
   DEVIATION: Real → Rat; `sq_continuous_at` re-proved with the
   book's own δ = min 1 (ε/(1+2|a|+1)) and estimate
   |x+a| ≤ |x-a| + 2|a|. (The book's script needs positivity,
   nlinarith, norm_num, ring_nf, and a nonexistent
   `div_mul_lt_iff` — Mathlib has div_lt_iff but no
   div_mul_lt_iff — so it fails even with Mathlib.)
   ============================================================ -/
namespace Ch8

def ContinuousAt (f : Rat -> Rat) (a : Rat) : Prop :=
  forall eps : Rat, eps > 0 ->
    exists delta : Rat, delta > 0 /\
      forall x : Rat, rabs (x - a) < delta -> rabs (f x - f a) < eps

theorem sq_continuous_at (a : Rat) : ContinuousAt (fun x => x * x) a := by
  intro eps heps
  have hA : (0:Rat) ≤ rabs a := rabs_nonneg a
  have hden : (0:Rat) < 1 + 2 * rabs a + 1 := by grind
  have hq : (0:Rat) < eps / (1 + 2 * rabs a + 1) := div_pos' heps hden
  refine ⟨min 1 (eps / (1 + 2 * rabs a + 1)), by grind, fun x hx => ?_⟩
  have hd1 : rabs (x - a) < 1 := by grind
  have hde : rabs (x - a) < eps / (1 + 2 * rabs a + 1) := by grind
  have hxa : rabs (x + a) < 1 + 2 * rabs a := by
    have h := rabs_add (x - a) (2 * a)
    have e : (x - a) + 2 * a = x + a := by grind
    rw [e] at h
    have h2 : rabs (2 * a) = 2 * rabs a := by
      have := rabs_mul 2 a
      have e2 : rabs (2 : Rat) = 2 := by simp only [rabs]; grind
      grind
    grind
  have hfact : x * x - a * a = (x - a) * (x + a) := by grind
  show rabs (x * x - a * a) < eps
  rw [hfact, rabs_mul]
  have hprod := mul_lt_mul_of_nonneg (rabs_nonneg (x - a)) hde
                  (rabs_nonneg (x + a)) hxa
  -- (ε/(2|a|+2)) * (2|a|+1) < ε since the quotient is positive
  have hcancel : eps / (1 + 2 * rabs a + 1) * (1 + 2 * rabs a + 1) = eps := by
    grind
  have hstep : eps / (1 + 2 * rabs a + 1) * (1 + 2 * rabs a + 1)
             - eps / (1 + 2 * rabs a + 1) * (1 + 2 * rabs a)
             = eps / (1 + 2 * rabs a + 1) := by grind
  grind

end Ch8

/- ============================================================
   §Ch10  The Derivative (book §10.1)
   DEVIATION: Real → Rat. `const_deriv` and `id_deriv` re-proved;
   note the book's own `const_deriv` script is wrong even
   Mathlib-side: it rewrites with `div_self` on `(c-c)/h`
   (numerator zero, so `div_self` — a/a = 1 — does not apply).
   `differentiable_implies_continuous` is left `sorry` BY THE BOOK
   (its comment says the full proof is omitted); we keep the sorry.
   ============================================================ -/
namespace Ch10

def HasDerivAt (f : Rat -> Rat) (x L : Rat) : Prop :=
  forall eps : Rat, eps > 0 ->
    exists delta : Rat, delta > 0 /\
      forall h : Rat, rabs h < delta -> h ≠ 0 ->
        rabs ((f (x + h) - f x) / h - L) < eps

theorem const_deriv (c x : Rat) : HasDerivAt (fun _ => c) x 0 := by
  intro eps heps
  refine ⟨1, by grind, fun h _ hne => ?_⟩
  show rabs ((c - c) / h - 0) < eps
  have key : (c - c) / h - 0 = 0 := by grind
  rw [key, rabs_zero]; exact heps

theorem id_deriv (x : Rat) : HasDerivAt id x 1 := by
  intro eps heps
  refine ⟨1, by grind, fun h _ hne => ?_⟩
  show rabs ((x + h - x) / h - 1) < eps
  have key : (x + h - x) / h - 1 = 0 := by grind
  rw [key, rabs_zero]; exact heps

open Ch8 in
-- BOOK'S OWN SORRY (Ch. 10 leanbox): "full proof uses:
-- f(x+h) - f(x) = h * ((f(x+h)-f(x))/h) -> 0".
theorem differentiable_implies_continuous (f : Rat -> Rat) (x L : Rat)
    (hf : HasDerivAt f x L) : ContinuousAt f x := by
  sorry

end Ch10

/- ============================================================
   §Ch11  Differentiation Rules (book §11.1)
   Both theorems are stated and left `sorry` BY THE BOOK.
   DEVIATION: Real → Rat only.
   ============================================================ -/
namespace Ch11
open Ch10

theorem product_rule (f g : Rat -> Rat) (x Lf Lg : Rat)
    (hf : HasDerivAt f x Lf) (hg : HasDerivAt g x Lg) :
    HasDerivAt (fun x => f x * g x) x (Lf * g x + f x * Lg) := by
  sorry  -- BOOK'S OWN SORRY: "Full proof requires bounding g near x"

theorem chain_rule (f g : Rat -> Rat) (x Lf Lg : Rat)
    (hg : HasDerivAt g x Lg) (hf : HasDerivAt f (g x) Lf) :
    HasDerivAt (f ∘ g) x (Lf * Lg) := by
  sorry  -- BOOK'S OWN SORRY: "Requires the local linearity formulation"

end Ch11

/- ============================================================
   §Ch14  Newton's Method (book §14.2)
   DEVIATION: the book declares `newton (f df : Real -> Real)`
   and then runs `#eval sqrtNewton 5 1.5` — impossible as printed:
   (a) `Real` doesn't exist here; (b) even with Mathlib, `Real` is
   noncomputable, so `#eval` of a Real-valued term FAILS. The
   book's own comment "(using Float approximation)" concedes the
   point; ported to Float, where it actually runs.
   ============================================================ -/
namespace Ch14

def newton (f df : Float -> Float) : Nat -> Float -> Float
  | 0,     x => x
  | n + 1, x => newton f df n (x - f x / df x)

def sqrtNewton (n : Nat) (x0 : Float) : Float :=
  newton (fun x => x * x - 2) (fun x => 2 * x) n x0

#eval sqrtNewton 5 1.5  -- prints 1.414214 (Float toString precision)

end Ch14

/- ============================================================
   §Ch15  The Riemann Integral (book §15.1)
   DEVIATIONS: Real → Rat; `List.Sorted` is Mathlib-only —
   replaced by core `List.Pairwise (· ≤ ·)` (same meaning).
   The `sorry`s inside upperSum/IsIntegrable are THE BOOK'S OWN
   (it labels the block a "sketch").
   ============================================================ -/
namespace Ch15

structure Partition (a b : Rat) where
  points : List Rat
  sorted : points.Pairwise (· ≤ ·)
  starts : points.head? = some a
  ends   : points.getLast? = some b

def subintervals {a b : Rat} (P : Partition a b) : List (Rat × Rat) :=
  P.points.zip P.points.tail

def upperSum {a b : Rat} (f : Rat -> Rat) (P : Partition a b) : Rat :=
  (subintervals P).foldl (fun acc (p : Rat × Rat) =>
    let Mi : Rat := sorry  -- BOOK'S OWN SORRY: "sup of f on [xi_prev, xi]"
    acc + Mi * (p.2 - p.1)) 0

def IsIntegrable (f : Rat -> Rat) (a b : Rat) : Prop :=
  exists I : Rat,
    forall eps : Rat, eps > 0 ->
      exists P : Partition a b,
        upperSum f P - I < eps /\ I - sorry < eps
        -- BOOK'S OWN SORRY (the lower sum is never defined)

end Ch15

/- ============================================================
   §Ch16  FTC (book §16.2)
   DEVIATION beyond Real → Rat: the book's statement references
   `integral f a b`, a function that IS NEVER DEFINED anywhere in
   the book — as printed the THEOREM STATEMENT itself fails with
   "unknown identifier 'integral'", independent of the (book's
   own) sorry proof. We add a sorry-stub `integral` so the
   statement can be elaborated at all.
   ============================================================ -/
namespace Ch16
open Ch8 Ch10 Ch15

def integral (f : Rat -> Rat) (a b : Rat) : Rat := sorry
  -- stub for the book's undefined `integral`

theorem ftc_part2 (f G : Rat -> Rat) (a b : Rat)
    (hcont : forall x, a <= x -> x <= b -> ContinuousAt f x)
    (hderiv : forall x, a < x -> x < b -> HasDerivAt G x (f x))
    (hint : IsIntegrable f a b) :
    integral f a b = G b - G a := by
  sorry  -- BOOK'S OWN SORRY: "Full proof requires the full Riemann
         -- integral machinery"

end Ch16

/- ============================================================
   §Ch21  Taylor Series for exp (book Ch. 21 leanbox)
   DEVIATIONS: (a) `Finset.sum (Finset.range (n+1))` — Finset is
   Mathlib-only; replaced by an equivalent structural recursion;
   (b) `Nat.factorial` does NOT exist in core Lean (Mathlib);
   defined here; (c) the two theorems `expTaylor_converges` and
   `exp_deriv` CANNOT EVEN BE STATED without Mathlib: they mention
   `Real.exp`, which has no counterpart in core Lean (and defining
   exp is precisely what the surrounding chapter has not done).
   They are therefore omitted — this is itself a finding: the book
   presents statements about an object it never constructs.
   ============================================================ -/
namespace Ch21

def factorial : Nat -> Nat
  | 0     => 1
  | n + 1 => (n + 1) * factorial n

def expTerm (k : Nat) (x : Rat) : Rat :=
  x ^ k / (factorial k : Rat)

def expTaylor : Nat -> Rat -> Rat
  | 0,     _ => 1
  | n + 1, x => expTaylor n x + expTerm (n + 1) x

end Ch21

/- ============================================================
   §Ch22  R^n (book §22.1)
   DEVIATIONS: (a) Real → Rat; (b) `Finset.sum Finset.univ` is
   Mathlib-only — replaced by recursion over Fin n; (c)
   `euclidNorm` requires `Real.sqrt`, which does not exist in core
   Lean and cannot exist over Rat — omitted (note: the book's
   Cauchy–Schwarz statement only needs normSq, so nothing is lost).
   The sorry in cauchy_schwarz is THE BOOK'S OWN.
   ============================================================ -/
namespace Ch22

def Vec (n : Nat) := Fin n -> Rat

def sumFin : (n : Nat) -> (Fin n -> Rat) -> Rat
  | 0,     _ => 0
  | n + 1, f => sumFin n (fun i => f i.castSucc) + f (Fin.last n)

def dotProduct {n : Nat} (v w : Vec n) : Rat :=
  sumFin n (fun i => v i * w i)

def normSq {n : Nat} (v : Vec n) : Rat :=
  dotProduct v v

theorem cauchy_schwarz {n : Nat} (v w : Vec n) :
    dotProduct v w ^ 2 <= normSq v * normSq w := by
  sorry  -- BOOK'S OWN SORRY ("Classic proof via discriminant";
         -- the book's partial script also fails: `positivity`)

/- Ch. 23 note: the book's `partialDeriv` "sketch"
     Classical.choose (HasDerivAt g (a i))
   is not just unfinished but ill-typed twice over:
   `HasDerivAt g (a i)` under-applies a 3-argument predicate, and
   `Classical.choose` takes a PROOF of `∃ x, p x`, not a Prop.
   Its `HasTotalDerivAt` definition depends on euclidNorm
   (Real.sqrt), so it cannot be ported to Rat; not reproduced. -/

end Ch22

/- ============================================================
   Part VII — Symboliculus (book Chs. 31–35)

   This is core-Lean Float code, so most of it is testable here.
   The book's unused pattern variables (su, s, t, step, ...) fire
   the unused-variables linter; silenced to keep the log readable.
   ============================================================ -/
set_option linter.unusedVariables false

namespace Symboliculus

-- Book Ch. 31 "The Expr Inductive Type": verbatim, compiles.
inductive Expr where
  | Const  : Float -> Expr               -- numeric constant
  | Var    : String -> Expr              -- variable (e.g. "x")
  | Add    : Expr -> Expr -> Expr
  | Sub    : Expr -> Expr -> Expr
  | Mul    : Expr -> Expr -> Expr
  | Div    : Expr -> Expr -> Expr
  | Pow    : Expr -> Expr -> Expr        -- e1 ^ e2
  | Neg    : Expr -> Expr
  | Sin    : Expr -> Expr
  | Cos    : Expr -> Expr
  | Tan    : Expr -> Expr
  | Exp    : Expr -> Expr                -- e^(...)
  | Ln     : Expr -> Expr
  | Abs    : Expr -> Expr
  deriving Repr, BEq

open Expr

-- Book Ch. 31 "Evaluation": verbatim, compiles.
def Expr.eval (env : String -> Float) : Expr -> Float
  | Const c        => c
  | Var   x        => env x
  | Add   e1 e2    => e1.eval env + e2.eval env
  | Sub   e1 e2    => e1.eval env - e2.eval env
  | Mul   e1 e2    => e1.eval env * e2.eval env
  | Div   e1 e2    => e1.eval env / e2.eval env
  | Pow   e1 e2    => Float.pow (e1.eval env) (e2.eval env)
  | Neg   e        => -(e.eval env)
  | Sin   e        => Float.sin (e.eval env)
  | Cos   e        => Float.cos (e.eval env)
  | Tan   e        => Float.tan (e.eval env)
  | Exp   e        => Float.exp (e.eval env)
  | Ln    e        => Float.log (e.eval env)
  | Abs   e        => Float.abs (e.eval env)

-- Book Ch. 31 "Pretty-Printing": `precedence` verbatim.
def Expr.precedence : Expr -> Nat
  | Add _ _ | Sub _ _ => 1
  | Mul _ _ | Div _ _ => 2
  | Neg _              => 3
  | Pow _ _            => 4
  | _                  => 10

-- DEVIATION: the book's pp calls `Int.ofFloat`, which does not
-- exist in Lean 4 core (error: unknown constant 'Int.ofFloat');
-- replaced with `Float.toInt64`. Everything else verbatim.
def Expr.pp : Expr -> String
  | Const c     => if c == Float.floor c then
                     toString c.toInt64
                   else toString c
  | Var x       => x
  | Add e1 e2   => s!"{e1.pp} + {e2.pp}"
  | Sub e1 e2   => s!"{e1.pp} - {paren e2 2}"
  | Mul e1 e2   => s!"{paren e1 2} * {paren e2 3}"
  | Div e1 e2   => s!"{paren e1 2} / {paren e2 3}"
  | Pow e1 e2   => s!"{paren e1 5}^{paren e2 5}"
  | Neg e       => s!"-{paren e 4}"
  | Sin e       => s!"sin({e.pp})"
  | Cos e       => s!"cos({e.pp})"
  | Tan e       => s!"tan({e.pp})"
  | Exp e       => s!"exp({e.pp})"
  | Ln  e       => s!"ln({e.pp})"
  | Abs e       => s!"|{e.pp}|"
where
  paren (e : Expr) (minPrec : Nat) :=
    if e.precedence < minPrec then s!"({e.pp})" else e.pp

-- Book Ch. 31 "Parsing": tokenise/parseExpr/... are the BOOK'S OWN
-- SORRIES ("full implementation in the Lake project").
inductive Token where
  | TNum  : Float  -> Token
  | TVar  : String -> Token
  | TPlus | TMinus | TStar | TSlash | TCaret
  | TLParen | TRParen | TEOF
  deriving Repr, BEq

def tokenise (s : String) : List Token := sorry

structure Parser where
  tokens : Array Token
  pos    : Nat

def Parser.peek (p : Parser) : Token :=
  p.tokens.getD p.pos Token.TEOF

def Parser.advance (p : Parser) : Parser :=
  { p with pos := p.pos + 1 }

def parseExpr  : Parser -> Except String (Expr × Parser) := sorry
def parseTerm  : Parser -> Except String (Expr × Parser) := sorry
def parseFactor : Parser -> Except String (Expr × Parser) := sorry

def parseStr (s : String) : Except String Expr :=
  match parseExpr { tokens := (tokenise s).toArray, pos := 0 } with
  | .ok (e, _) => .ok e
  | .error msg => .error msg

/- Book Ch. 31 "Algebraic Simplification".
   DEVIATION: the book pattern-matches on Float LITERALS
   (`| Add e (Const 0) => ...`) — Lean rejects this outright
   ("Dependent elimination failed": Float literals are not
   constructor patterns, since `0 : Float` is `Float.ofScientific
   0 false 0`, not a constructor). Rewritten with BEq guards; rule
   order preserved. -/
def Expr.simplify : Expr -> Expr
  -- Arithmetic on constants
  | Add (Const a) (Const b)  => Const (a + b)
  | Sub (Const a) (Const b)  => Const (a - b)
  | Mul (Const a) (Const b)  => Const (a * b)
  | Div (Const a) (Const b)  =>
      if b != 0 then Const (a / b) else Div (Const a) (Const b)
  -- Additive identity
  | Add e (Const c)          =>
      if c == 0 then e.simplify else Add e.simplify (Const c)
  | Add (Const c) e          =>
      if c == 0 then e.simplify else Add (Const c) e.simplify
  -- Multiplicative identity / zero
  | Mul e (Const c)          =>
      if c == 1 then e.simplify
      else if c == 0 then Const 0
      else Mul e.simplify (Const c)
  | Mul (Const c) e          =>
      if c == 1 then e.simplify
      else if c == 0 then Const 0
      else Mul (Const c) e.simplify
  -- Power rules
  | Pow e (Const c)          =>
      if c == 1 then e.simplify
      else if c == 0 then Const 1
      else if e == Const 1 then Const 1
      else Pow e.simplify (Const c)
  | Pow (Const c) e          =>
      if c == 1 then Const 1 else Pow (Const c) e.simplify
  -- Double negation
  | Neg (Neg e)              => e.simplify
  -- Recurse
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

-- Book "fullSimplify": verbatim, compiles.
def Expr.fullSimplify (e : Expr) (fuel : Nat := 20) : Expr :=
  match fuel with
  | 0     => e
  | n + 1 =>
    let e' := e.simplify
    if e' == e then e else e'.fullSimplify n

-- Book Ch. 32 "DiffStep": verbatim, compiles.
inductive DiffStep where
  | ConstRule   : DiffStep                          -- d/dx c = 0
  | VarRule     : DiffStep                          -- d/dx x = 1
  | VarOther    : DiffStep                          -- d/dx y = 0 (y != x)
  | SumRule     : DiffStep -> DiffStep -> DiffStep  -- (u+v)' = u'+v'
  | SubRule     : DiffStep -> DiffStep -> DiffStep
  | ProductRule : DiffStep -> DiffStep -> DiffStep  -- (uv)' = u'v+uv'
  | QuotRule    : DiffStep -> DiffStep -> DiffStep  -- (u/v)' = (u'v-uv')/v^2
  | ChainRule   : String   -> DiffStep -> DiffStep  -- outer fn, inner deriv
  | PowerRule   : DiffStep                          -- d/dx x^n = nx^{n-1}
  | NegRule     : DiffStep -> DiffStep
  deriving Repr

/- DEVIATION applying to `diff` and everything below: the book's
   plain-named functions (diff, directLookup, ...) pattern-match on
   bare constructor names `Const/Add/Mul/...` with no `open Expr` in
   sight. Without an open, the names are unknown; with `open Expr`,
   the patterns are AMBIGUOUS against the arithmetic type classes
   `_root_.Add/Mul/Pow/Neg` ("ambiguous pattern" error). We use
   anonymous-constructor dot-patterns (.Add, .Mul, ...) instead. -/

-- Book Ch. 32 "diff": as printed, plus the pattern fix above
-- (note: the PowerRule case
-- computes but then DISCARDS the sub-derivation `su`, so power-rule
-- steps lose their inner trace — see the #eval demonstration below).
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
  | .Abs _       => (Const 0, .ConstRule)  -- simplified; full version uses sign

-- Book Ch. 32 "DiffStep.render": verbatim, compiles.
def DiffStep.render (orig result : Expr) : DiffStep -> String
  | .ConstRule    => s!"d/dx({orig.pp}) = 0  [constant rule]"
  | .VarRule      => s!"d/dx({orig.pp}) = 1  [variable rule]"
  | .VarOther     => s!"d/dx({orig.pp}) = 0  [independent variable]"
  | .NegRule s    =>
      s!"Negate: d/dx(-u) = -(d/dx u)\n  " ++ s.render orig result
  | .SumRule s t  =>
      s!"Sum rule: d/dx(u + v) = d/dx(u) + d/dx(v)"
  | .ProductRule s t =>
      s!"Product rule: d/dx(u*v) = u'*v + u*v'"
  | .QuotRule s t =>
      s!"Quotient rule: d/dx(u/v) = (u'v - uv') / v^2"
  | .ChainRule fn s =>
      s!"Chain rule on {fn}: d/dx({fn}(u)) = {fn}'(u) * d/dx(u)"
  | .PowerRule    =>
      s!"Power rule: d/dx(u^n) = n * u^(n-1) * u'"
  | _             => s!"[step applied to {orig.pp}]"

/- Book Ch. 33. DEVIATION — as printed, this chapter cannot compile:
   * `tryUSub` calls `substVar`, `substExpr`, `isInTermsOf`, which
     are NEVER DEFINED anywhere in the book (unknown identifiers);
   * `innerFunctions` is used by tryUSub before its definition;
   * `liatePriority` matches `Arctan _ | Arcsin _` — constructors
     that do not exist in Expr (adding them is exercise 2 of Ch. 32);
   * `tryIBP`/`sumStrategy`/`constMulStrategy`/`integrate` are
     mutually recursive with no `mutual` block, and the recursion is
     not structurally decreasing, so Lean cannot accept them as
     total `def`s — they must be `partial def` (which also means the
     book's implicit termination claim is unproven);
   * `integrate` lists `partialFracStrategy` and `trigReduceStrategy`
     among its strategies, but the book never defines them (they are
     exercises 2–3 of Ch. 33): unknown identifiers as printed.
   Minimal stubs and reorderings below make the architecture
   compile; semantics of the undefined helpers is our best reading. -/

inductive IntStep where
  | DirectLookup  : String -> IntStep
  | ConstMul      : IntStep -> IntStep
  | SumRule       : IntStep -> IntStep -> IntStep
  | USub          : Expr -> Expr -> IntStep -> IntStep
  | IBP           : Expr -> Expr -> IntStep -> IntStep -> IntStep
  | PartialFrac   : List (Expr × Expr) -> List IntStep -> IntStep
  | TrigSub       : String -> Expr -> IntStep -> IntStep
  | TrigReduce    : IntStep -> IntStep
  | Failed        : IntStep
  deriving Repr

def Strategy := String -> Expr -> Option (Expr × IntStep)

-- Book "directLookup": verbatim, compiles.
def directLookup (x : String) : Expr -> Option (Expr × IntStep)
  | .Const c           =>
      some (Mul (Const c) (Var x), .DirectLookup s!"∫{c} dx = {c}x")
  | .Var y             =>
      if y == x
      then some (Div (Pow (Var x) (Const 2)) (Const 2),
                 .DirectLookup "∫x dx = x²/2")
      else none
  | .Sin (Var y)       =>
      if y == x
      then some (Neg (Cos (Var x)), .DirectLookup "∫sin(x) dx = -cos(x)")
      else none
  | .Cos (Var y)       =>
      if y == x
      then some (Sin (Var x), .DirectLookup "∫cos(x) dx = sin(x)")
      else none
  | .Exp (Var y)       =>
      if y == x
      then some (Exp (Var x), .DirectLookup "∫eˣ dx = eˣ")
      else none
  | .Pow (Var y) (Const n) =>
      if y == x && n != -1
      then some (Div (Pow (Var x) (Const (n+1))) (Const (n+1)),
                 .DirectLookup s!"∫xⁿ dx = xⁿ⁺¹/(n+1)")
      else none
  | _                 => none

-- Book "innerFunctions" (moved BEFORE tryUSub; the book uses it
-- before defining it). DEVIATION: the book's alternative
-- `| Pow u _ | Pow _ u => [u]` is REJECTED by Lean — the second
-- disjunct cannot match anything the first does not already match
-- ("Redundant alternative" error); kept the first disjunct only.
def innerFunctions : Expr -> List Expr
  | .Sin u | .Cos u | .Tan u | .Exp u | .Ln u => [u]
  | .Pow u _                               => [u]
  | .Mul u v | .Add u v                    => innerFunctions u ++ innerFunctions v
  | _                                    => []

-- DEVIATION: the following three helpers are called by the book's
-- tryUSub but never defined in the book. Minimal implementations.
def varsOf : Expr -> List String
  | .Const _   => []
  | .Var y     => [y]
  | .Add a b | .Sub a b | .Mul a b | .Div a b | .Pow a b => varsOf a ++ varsOf b
  | .Neg a | .Sin a | .Cos a | .Tan a | .Exp a | .Ln a | .Abs a => varsOf a

/-- Rename variable `x` to `u`. -/
def substVar (x u : String) : Expr -> Expr
  | .Const c   => Const c
  | .Var y     => if y == x then Var u else Var y
  | .Add a b   => Add (substVar x u a) (substVar x u b)
  | .Sub a b   => Sub (substVar x u a) (substVar x u b)
  | .Mul a b   => Mul (substVar x u a) (substVar x u b)
  | .Div a b   => Div (substVar x u a) (substVar x u b)
  | .Pow a b   => Pow (substVar x u a) (substVar x u b)
  | .Neg a     => Neg (substVar x u a)
  | .Sin a     => Sin (substVar x u a)
  | .Cos a     => Cos (substVar x u a)
  | .Tan a     => Tan (substVar x u a)
  | .Exp a     => Exp (substVar x u a)
  | .Ln  a     => Ln  (substVar x u a)
  | .Abs a     => Abs (substVar x u a)

/-- Replace variable `u` by the expression `repl`. -/
def substExpr (u : String) (repl : Expr) : Expr -> Expr
  | .Const c   => Const c
  | .Var y     => if y == u then repl else Var y
  | .Add a b   => Add (substExpr u repl a) (substExpr u repl b)
  | .Sub a b   => Sub (substExpr u repl a) (substExpr u repl b)
  | .Mul a b   => Mul (substExpr u repl a) (substExpr u repl b)
  | .Div a b   => Div (substExpr u repl a) (substExpr u repl b)
  | .Pow a b   => Pow (substExpr u repl a) (substExpr u repl b)
  | .Neg a     => Neg (substExpr u repl a)
  | .Sin a     => Sin (substExpr u repl a)
  | .Cos a     => Cos (substExpr u repl a)
  | .Tan a     => Tan (substExpr u repl a)
  | .Exp a     => Exp (substExpr u repl a)
  | .Ln  a     => Ln  (substExpr u repl a)
  | .Abs a     => Abs (substExpr u repl a)

/-- Crude reading of "e is expressed in terms of u": every variable
    of e already occurs in u. -/
def isInTermsOf (u e : Expr) : Bool :=
  (varsOf e).all (fun v => (varsOf u).contains v)

-- Book "tryUSub": with the helpers above it compiles; note it can
-- essentially never fire, since `fullSimplify` cannot cancel g'(x)
-- (see FINDINGS in the review).
def tryUSub (x : String) (e : Expr) : Option (Expr × IntStep) :=
  let candidates := innerFunctions e
  candidates.findSome? fun u =>
    let du := (diff x u).1
    let reduced := (Div e du).fullSimplify
    if isInTermsOf u reduced then
      match directLookup "u" (substVar x "u" reduced) with
      | some (antideriv, step) =>
          some ((substExpr "u" u antideriv).fullSimplify,
                .USub u du step)
      | none => none
    else none

-- Book "liatePriority": DEVIATION — the Arctan/Arcsin alternative
-- is removed (no such Expr constructors exist), and `Var _` is added
-- at algebraic priority 2 (the book originally gave a bare `x`
-- priority 5, BELOW Exp (4), which made the flagship ∫ x·eˣ example
-- fail — IBP picked u = eˣ, dv = x). The book has been updated to
-- match this fixed version.
def liatePriority : Expr -> Nat
  | .Ln _               => 0   -- highest: logarithm
  | .Pow (Var _) _      => 2   -- algebraic (polynomial)
  | .Var _              => 2   -- algebraic (bare x)
  | .Sin _ | .Cos _      => 3   -- trigonometric
  | .Exp _              => 4   -- exponential (lowest priority)
  | _                  => 5

-- DEVIATION: stubs for the two strategies `integrate` references
-- but the book never defines (left as exercises).
def partialFracStrategy : Strategy := fun _ _ => none
def trigReduceStrategy  : Strategy := fun _ _ => none

-- DEVIATION: mutual + partial (see block comment above).
mutual

partial def tryIBP (x : String) (e : Expr) : Option (Expr × IntStep) :=
  match e with
  | .Mul u v =>
    let (uPart, dvPart) :=
      if liatePriority u <= liatePriority v
      then (u, v)
      else (v, u)
    let uPrime := (diff x uPart).1
    match directLookup x dvPart with
    | some (vPart, _) =>
        let remaining := (Mul vPart uPrime).fullSimplify
        match integrate x remaining with
        | some (intRemainder, step) =>
            let result := Sub (Mul uPart vPart) intRemainder
            some (result.fullSimplify,
                  .IBP uPart dvPart (.DirectLookup "") step)
        | none => none
    | none => none
  | _ => none

partial def integrate (x : String) (e : Expr) : Option (Expr × IntStep) :=
  let strategies : List Strategy :=
    [ directLookup,
      constMulStrategy,
      sumStrategy,
      tryUSub,
      tryIBP,
      partialFracStrategy,
      trigReduceStrategy ]
  strategies.findSome? (· x e)

partial def sumStrategy (x : String) : Expr -> Option (Expr × IntStep)
  | .Add u v =>
      match integrate x u, integrate x v with
      | some (U, su), some (V, sv) =>
          some ((Add U V).fullSimplify, .SumRule su sv)
      | _, _ => none
  | _ => none

partial def constMulStrategy (x : String) : Expr -> Option (Expr × IntStep)
  | .Mul (Const c) e =>
      match integrate x e with
      | some (E, s) => some ((Mul (Const c) E).fullSimplify, .ConstMul s)
      | none        => none
  | .Mul e (Const c) =>
      match integrate x e with
      | some (E, s) => some ((Mul (Const c) E).fullSimplify, .ConstMul s)
      | none        => none
  | _ => none

end

-- Book Ch. 34 "SolveTrace": verbatim.
inductive SolveTrace where
  | Leaf   : String -> Expr -> SolveTrace          -- rule name, result
  | Node   : String -> Expr -> List SolveTrace -> SolveTrace

-- Book "DiffStep.toTrace": DEVIATION — the book's match omits the
-- `SubRule` case entirely (error: missing cases as printed); added.
def DiffStep.toTrace (e result : Expr) : DiffStep -> SolveTrace
  | .ConstRule    =>
      .Leaf "Constant Rule" (Const 0)
  | .VarRule      =>
      .Leaf "Variable Rule" (Const 1)
  | .VarOther     =>
      .Leaf "Independent Variable" (Const 0)
  | .SumRule s t  =>
      .Node "Sum Rule" result [s.toTrace e result, t.toTrace e result]
  | .SubRule s t  =>  -- MISSING FROM THE BOOK
      .Node "Difference Rule" result [s.toTrace e result, t.toTrace e result]
  | .ProductRule s t =>
      .Node "Product Rule" result [s.toTrace e result, t.toTrace e result]
  | .QuotRule s t =>
      .Node "Quotient Rule" result [s.toTrace e result, t.toTrace e result]
  | .ChainRule fn s =>
      .Node s!"Chain Rule ({fn})" result [s.toTrace e result]
  | .PowerRule    =>
      .Leaf "Power Rule" result
  | .NegRule s    =>
      .Node "Negation Rule" result [s.toTrace e result]

-- Book "renderLines"/"render": DEVIATIONS — `String.replicate` does
-- not exist in core (→ `"".pushn`), `List.bind` does not exist in
-- v4.28 core (→ `List.flatMap`).
def SolveTrace.renderLines (depth : Nat := 0) : SolveTrace -> List String
  | .Leaf rule result =>
      ["".pushn ' ' (depth * 2) ++ s!"• {rule}: {result.pp}"]
  | .Node rule result children =>
      let header := "".pushn ' ' (depth * 2)
                      ++ s!"▶ {rule} → {result.pp}"
      let childLines := children.flatMap (·.renderLines (depth + 1))
      header :: childLines

def SolveTrace.render (t : SolveTrace) : String :=
  "\n".intercalate t.renderLines

-- Book "solveDerivative"/"solveIntegral": verbatim.
def solveDerivative (x : String) (e : Expr) : String :=
  let (result, step) := diff x e
  let trace := step.toTrace e result
  s!"d/dx({e.pp}) = {result.pp}\n\nSteps:\n{trace.render}"

def solveIntegral (x : String) (e : Expr) : String :=
  match integrate x e with
  | some (result, step) =>
      s!"∫({e.pp}) dx = {result.pp} + C\n\n(step trace available)"
  | none =>
      s!"∫({e.pp}) dx — no elementary antiderivative found"

/- Behavioural checks: the book's printed sample outputs (Chs. 34–35)
   have been updated to match EXACTLY what the fixed code below
   prints. Note two documented limitations, now acknowledged in the
   book's prose: (a) `toTrace` threads the TOP-LEVEL result into
   every compound node (DiffStep does not record intermediate
   results); (b) `diff`'s Pow case returns the LEAF `.PowerRule`,
   discarding the inner trace. With the fixed liatePriority,
   ∫ x·exp(x) succeeds and prints `x * exp(x) - exp(x)` (which is
   (x-1)eˣ mathematically, but the engine does not factor). -/
#eval solveDerivative "x" (Expr.Mul (Expr.Var "x") (Expr.Sin (Expr.Var "x")))
#eval solveIntegral "x" (Expr.Mul (Expr.Var "x") (Expr.Exp (Expr.Var "x")))
#eval solveDerivative "x"
  (Expr.Mul (Expr.Pow (Expr.Var "x") (Expr.Const 2)) (Expr.Sin (Expr.Var "x")))

/- Book Ch. 35 (Main.lean). DEVIATION: the book declares
   `structure Args` with a field `mode : Mode := .Diff` BEFORE
   declaring `inductive Mode` — unknown identifier as printed;
   reordered. Rest verbatim. -/

def usage : String :=
  "symboliculus [--diff | --integral] --expr <expr> --var <var> [--steps]"

inductive Mode where | Diff | Integral

structure Args where
  mode  : Mode := .Diff
  expr  : String := ""
  var   : String := "x"
  steps : Bool   := false

def parseArgs : List String -> Except String Args
  | []         => .ok {}
  | "--diff"   :: rest => do let a <- parseArgs rest; .ok { a with mode := .Diff }
  | "--integral"::rest => do let a <- parseArgs rest; .ok { a with mode := .Integral }
  | "--expr" :: e :: rest =>
      do let a <- parseArgs rest; .ok { a with expr := e }
  | "--var"  :: v :: rest =>
      do let a <- parseArgs rest; .ok { a with var := v }
  | "--steps" :: rest =>
      do let a <- parseArgs rest; .ok { a with steps := true }
  | s :: _ => .error s!"Unknown argument: {s}\n{usage}"

def main (args : List String) : IO Unit := do
  match parseArgs args with
  | .error msg => IO.eprintln msg
  | .ok a =>
    if a.expr == "" then
      IO.eprintln s!"No expression given.\n{usage}"
    else
      match parseStr a.expr with
      | .error msg => IO.eprintln s!"Parse error: {msg}"
      | .ok e =>
        match a.mode with
        | .Diff =>
            let output := if a.steps
                          then solveDerivative a.var e
                          else
                            let (result, _) := diff a.var e
                            s!"d/d{a.var}({e.pp}) = {result.pp}"
            IO.println output
        | .Integral =>
            let output := if a.steps
                          then solveIntegral a.var e
                          else
                            match integrate a.var e with
                            | some (result, _) =>
                                s!"∫({e.pp}) d{a.var} = {result.pp} + C"
                            | none =>
                                s!"∫({e.pp}) d{a.var} = (no elementary form found)"
            IO.println output

/- Ch. 36 note: the book's rewritten Section 36.1 now defines a
   real-valued interpretation `Expr.evalR` and proves the honest
   rule-level correctness lemmas against Mathlib's HasDerivAt;
   those listings are Mathlib-dependent and are verified in
   CalculusMathlibVerification.lean (namespace VCM36). -/

end Symboliculus

/- ============================================================
   §PrimerAppendix — Appendix A "A Lean 4 Primer": every CORE-LEAN
   example printed in the appendix, compiled. (The Mathlib-tactic
   examples of the appendix are compiled in
   CalculusMathlibVerification.lean, namespace VCMPrimer.)
   ============================================================ -/
namespace PrimerAppendix

-- ---- inductive ----
inductive Tree where
  | leaf : Tree
  | node : Tree -> Tree -> Tree
  deriving Repr

-- ---- def by pattern matching (structural recursion) ----
def Tree.size : Tree -> Nat
  | .leaf     => 1
  | .node l r => l.size + r.size

-- ---- type classes and instances ----
structure Complex where
  re : Float
  im : Float
  deriving Repr

instance : Add Complex where
  add a b := ⟨a.re + b.re, a.im + b.im⟩

#eval (Complex.mk 1 2) + (Complex.mk 3 4)
-- { re := 4.000000, im := 6.000000 }

-- ---- @[simp] ----
@[simp] theorem Tree.size_node (l r : Tree) :
    (Tree.node l r).size = l.size + r.size := rfl

example (t : Tree) : (Tree.node t .leaf).size = t.size + 1 := by
  simp [Tree.size]

-- ---- rfl ----
example : 2 + 3 = 5 := rfl

-- ---- intro / exact / apply ----
example (p q : Prop) : p -> (p -> q) -> q := by
  intro hp h
  apply h
  exact hp

example (p q : Prop) (hp : p) (h : p -> q) : q := h hp  -- same, as a term

-- ---- rw ----
example (a b : Nat) (h : a = b) : a + a = b + b := by rw [h]

-- ---- simp ----
example (n : Nat) : (n + 0) * 1 = n := by simp

-- ---- induction ... with ----
theorem zero_add_nat (n : Nat) : 0 + n = n := by
  induction n with
  | zero      => rfl
  | succ n ih => rw [Nat.add_succ, ih]

-- ...and its desugaring: applying the recursor directly. (The
-- `show` re-states the goal in beta-reduced form so `rw` can see it.)
theorem zero_add_nat' (n : Nat) : 0 + n = n :=
  Nat.rec (motive := fun n => 0 + n = n)
    rfl                                     -- base case
    (fun n ih => by                         -- step case
      show 0 + (n + 1) = n + 1
      rw [Nat.add_succ, ih])
    n

-- ---- cases ----
example (p q : Prop) (h : p ∨ q) : q ∨ p := by
  cases h with
  | inl hp => exact Or.inr hp
  | inr hq => exact Or.inl hq

-- ---- obtain / rcases ----
example (h : ∃ n : Nat, n > 5) : ∃ n : Nat, n > 3 := by
  obtain ⟨n, hn⟩ := h
  exact ⟨n, by omega⟩

-- ...and the desugaring: a match on the anonymous constructor
example (h : ∃ n : Nat, n > 5) : ∃ n : Nat, n > 3 :=
  match h with
  | ⟨n, hn⟩ => ⟨n, by omega⟩

-- ...or, fully explicit, the eliminator:
example (h : ∃ n : Nat, n > 5) : ∃ n : Nat, n > 3 :=
  Exists.elim h (fun n hn => ⟨n, by omega⟩)

-- rcases with a nested pattern
example (h : ∃ n : Nat, n > 5 ∧ n < 10) : ∃ n : Nat, n < 10 := by
  rcases h with ⟨n, hgt, hlt⟩
  exact ⟨n, hlt⟩

-- ---- constructor ----
example (p q : Prop) (hp : p) (hq : q) : p ∧ q := by
  constructor
  · exact hp
  · exact hq

-- ---- calc ----
example (a b c : Nat) (h1 : a ≤ b) (h2 : b ≤ c) : a ≤ c + 1 := by
  calc a ≤ b     := h1
    _    ≤ c     := h2
    _    ≤ c + 1 := Nat.le_succ c

-- ...and its desugaring: chained Trans.trans applications
example (a b c : Nat) (h1 : a ≤ b) (h2 : b ≤ c) : a ≤ c + 1 :=
  Trans.trans (Trans.trans h1 h2) (Nat.le_succ c)

-- ---- suffices ----
example (n : Nat) (h : n ≥ 10) : n > 3 := by
  suffices hs : n > 5 by omega
  omega

-- ---- omega ----
example (a b : Nat) (h : a + 2 * b = 10) (hb : b ≥ 3) : a ≤ 4 := by
  omega

-- ---- decide ----
example : 17 * 3 = 51 := by decide
example : ∀ n : Fin 5, n.val < 10 := by decide

-- ---- grind ----
example (a b : Rat) (h : a < b) : a - b < 0 := by grind

-- ---- have / show ----
example (a b : Nat) (h : a = b) : b = a := by
  have h2 : a = b := h
  show b = a
  exact h2.symm

-- ---- funext ----
example (f g : Nat -> Nat) (h : ∀ n, f n = g n) : f = g := funext h

-- ---- Quot / Quot.mk / Quot.lift / Quot.sound ----
def parityRel (m n : Nat) : Prop := m % 2 = n % 2

def Parity : Type := Quot parityRel

def Parity.ofNat (n : Nat) : Parity := Quot.mk parityRel n

-- Descend a function to the quotient: needs a respect proof.
def Parity.isEven : Parity -> Bool :=
  Quot.lift (fun n => n % 2 == 0)
    (fun a b h => by simp [parityRel] at h; simp [h])

-- Equate two representatives: Quot.sound turns relatedness into
-- equality of equivalence classes.
theorem parity_two_zero : Parity.ofNat 2 = Parity.ofNat 0 :=
  Quot.sound (by simp [parityRel])

#eval (Parity.ofNat 6).isEven  -- true

end PrimerAppendix

end VC
