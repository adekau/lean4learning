inductive MyNat where
  | zero : MyNat
  | succ : MyNat → MyNat
  deriving Repr

theorem MyNat.ind (P : MyNat → Prop) (h0 : P .zero) (hs : ∀ n : MyNat, P n → P (.succ n))
    : ∀ n : MyNat, P n := by
  intro n
  induction n with
  | zero => exact h0
  | succ n ih => exact hs n ih

@[simp] def MyNat.add : MyNat → MyNat → MyNat
  | n     , .zero   => n
  | n     , .succ m => .succ (n.add m)

def MyNat.one := MyNat.succ .zero
def MyNat.two := MyNat.succ .one
def MyNat.three := MyNat.succ .two

#eval MyNat.add .two .three -- .succ 5 times

@[simp] def MyNat.mul : MyNat → MyNat → MyNat
  | _     , .zero   => .zero
  | n     , .succ m => .add (.mul n m) n

#eval MyNat.mul .two .three -- .succ 6 times

instance : Add MyNat := ⟨MyNat.add⟩
instance : Mul MyNat := ⟨MyNat.mul⟩

@[simp] theorem MyNat.add_def (m n : MyNat) : m + n = MyNat.add m n := rfl
@[simp] theorem MyNat.mul_def (m n : MyNat) : m * n = MyNat.mul m n := rfl

theorem MyNat.zero_add (n : MyNat) : .zero + n = n := by
  induction n with
  | zero      => rfl
  | succ n ih => simp_all [MyNat.add]

theorem MyNat.add_zero (n : MyNat) : n + .zero = n := by
  simp [MyNat.add]

theorem MyNat.zero_mul (n : MyNat) : .zero * n = .zero := by
  induction n with
  | zero      => rfl
  | succ n ih => simp_all [MyNat.mul]

theorem MyNat.succ_add (n m : MyNat) : n.succ.add m = (n.add m).succ := by
  induction m with
  | zero => rfl
  | succ m ih =>
      simp [MyNat.add, ih]


theorem MyNat.add_comm (n m : MyNat) : m + n = n + m:= by
  induction n with
  | zero      => rw [MyNat.zero_add]; rfl
  | succ n ih => simp_all [MyNat.add, MyNat.succ_add]

theorem MyNat.add_assoc (a b c : MyNat) : (a + b) + c = a + (b + c) := by
  induction c with
  | zero => rfl
  | succ c ih => simp_all [MyNat.add]

theorem MyNat.no_overflow (n m : MyNat) : n + m.succ ≠ n := by
  induction n with
  | zero      => simp [MyNat.add]
  | succ n ih => simp_all [MyNat.add, MyNat.succ_add]

theorem MyNat.add_eq_self (n k : MyNat) : n + k = n → k = .zero := by
  cases k with
  | zero   => intros; rfl
  | succ k => intro h; exact absurd h (MyNat.no_overflow n k)

theorem MyNat.add_eq_zero_left {a b : MyNat} (h : a + b = .zero) : a = .zero := by
  cases a with
  | zero => rfl
  | succ a =>
    cases b with
    | zero => contradiction
    | succ b => contradiction

@[simp] def MyNat.le (m n : MyNat) : Prop := ∃ k : MyNat, m + k = n
def MyNat.lt (m n : MyNat) : Prop := m.le n ∧ m ≠ n

instance : LE MyNat := ⟨MyNat.le⟩
@[simp] theorem MyNat.le_def (m n : MyNat) : (m ≤ n) = MyNat.le m n := by rfl

theorem MyNat.le_refl (n : MyNat) : n ≤ n := ⟨.zero, by rfl⟩
theorem MyNat.le_antisymm (n m : MyNat) : n ≤ m → m ≤ n → n = m := by
  intro ⟨k, hn⟩ ⟨j, hm⟩
  have h := hn ▸ hm
  rw [MyNat.add_assoc] at h
  have hkj : k + j = .zero := MyNat.add_eq_self n _ h
  have hk0 : k = .zero := MyNat.add_eq_zero_left hkj
  rw [←hn, hk0, MyNat.add_zero]

theorem MyNat.le_trans (a b c : MyNat) : a ≤ b → b ≤ c → a ≤ c := by
  intro ⟨k, hk⟩ ⟨j, hj⟩
  have h := hk ▸ hj
  refine ⟨k + j, ?hkj⟩
  case hkj => rwa [MyNat.add_assoc] at h

theorem MyNat.le_zero_mp (n : MyNat) : n ≤ .zero → n = .zero := by
  intro ⟨k, hk⟩
  exact MyNat.add_eq_zero_left hk

theorem MyNat.not_lt_zero (n : MyNat) : ¬(MyNat.lt n .zero) := by
  apply Not.intro
  intro h
  simp [MyNat.lt] at h
  obtain ⟨k, hk⟩ := h.left
  change n + k = .zero at hk
  have h0 := MyNat.add_eq_zero_left hk
  exact absurd h0 h.right

theorem even_of_double (n : Nat) : 2 ∣ (n + n) := by
  suffices h : n + n = 2 * n from by
    simp [Dvd.dvd]
    exact ⟨n, h⟩
  omega

#check Nat.lt_or_eq_of_le

theorem MyNat.lt_or_eq_of_le {n m : MyNat} (h : n ≤ m) : n.lt m ∨ n = m := by
  simp [MyNat.le] at h
  simp [MyNat.lt]
  apply Or.intro_right
  obtain ⟨k, hk⟩ := h
  induction k with
  | zero => simp at hk; assumption
  | succ k ih => sorry

theorem MyNat.strong_ind (P : MyNat → Prop)
  (step : ∀ n : MyNat, (∀ k : MyNat, k.lt n → P k) → P n) :
    ∀ n, P n := by
suffices h : ∀ n, ∀ k, k ≤ n → P k from by
  intro n
  have refl_eq := h n n
  exact refl_eq (MyNat.le_refl n)
intro n
induction n with
| zero =>
  intro k hk
  have hkz := MyNat.le_zero_mp k hk
  subst hkz
  have : ∀ (k : MyNat), k.lt zero → P k := fun k hlt => by
    exact absurd hlt (MyNat.not_lt_zero k)
  exact step .zero this
| succ n ih =>
  intro k hk
  sorry
