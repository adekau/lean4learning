inductive MyNat where
  | zero : MyNat
  | succ : MyNat → MyNat
  deriving Repr, DecidableEq

def MyNat.pred : MyNat → MyNat
  | zero    => zero
  | succ n  => n

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

instance : LT MyNat := ⟨MyNat.lt⟩
instance : LE MyNat := ⟨MyNat.le⟩
@[simp] theorem MyNat.le_def (m n : MyNat) : (m ≤ n) = MyNat.le m n := by rfl

theorem MyNat.zero_le (n : MyNat) : .zero ≤ n := by
  cases n
  · simp
    exact ⟨.zero, by rfl⟩
  · simp
    rename_i n
    refine ⟨n.succ, ?_⟩
    apply MyNat.zero_add

inductive MyNat.le2 (n : MyNat) : MyNat → Prop where
  | refl      : MyNat.le2 n n
  | step {m}  : MyNat.le2 n m → MyNat.le2 n m.succ

-- n.succ ≤ m implies n ≤ m (weakening)
theorem MyNat.le2.le_of_succ_le {n m : MyNat} (h : n.succ.le2 m) : n.le2 m := by
  induction h with
  | refl      => exact .step .refl      -- n ≤ n.succ
  | step _ ih => exact .step ih         -- n ≤ k, so n ≤ k.succ

theorem MyNat.le_of_succ_le_succ {n m : MyNat} (h : n.succ.le2 m.succ) : n.le2 m := by
  cases h with
  | refl      => exact .refl
  | step h    => exact h.le_of_succ_le  -- need one more helper

theorem MyNat.not_succ_le_self (n : MyNat) : ¬(n.succ.le2 n) := by
  induction n with
  | zero      => intro h; cases h       -- MyNat.le 1 0, no constructors apply
  | succ n ih =>
    intro h
    exact ih (MyNat.le_of_succ_le_succ h)     -- h : n.succ ≤ n, apply inductive hypothesis

-- theorem MyNat.zero_le : (n : MyNat) → MyNat.le .zero n
--   | zero    => MyNat.le.refl
--   | succ n  => MyNat.le.step (zero_le n)

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

theorem MyNat.add_comm_succ_right (n m : MyNat) : n.succ.add m = n.add m.succ := by
  induction m with
  | zero => rfl
  | succ m ih =>
    simp [MyNat.add]
    exact ih

theorem MyNat.add_comm_succ_left (n m : MyNat) : n.succ.add m = (n.add m).succ := by
  induction m with
  | zero => rfl
  | succ m ih =>
    simp [MyNat.add]
    exact ih

theorem MyNat.lt_or_eq_of_le {n m : MyNat} (h : n ≤ m) : n.lt m ∨ n = m := by
  obtain ⟨k, hk⟩ := h
  induction k with
  | zero =>
    apply Or.inr
    simpa [MyNat.add] using hk
  | succ k ih =>
    apply Or.inl
    simp [MyNat.le, MyNat.lt]
    refine ⟨⟨k.succ, hk⟩, ?_⟩
    apply Not.intro
    intro heq
    subst heq
    have := MyNat.add_eq_self n k.succ hk
    contradiction

theorem MyNat.le_succ {n m : MyNat} (h : n ≤ m) : n ≤ m.succ := by
  simp_all
  obtain ⟨k, hk⟩ := h
  refine ⟨k.succ, ?_⟩
  subst hk
  simp only [MyNat.add]

theorem MyNat.lt_not_succ {n m : MyNat} (h : n.lt m) : ¬(n = m.succ) := by
  obtain ⟨⟨k, hk⟩, hne⟩ := h
  cases k with
  | zero => simp at hk; contradiction
  | succ k =>
    intro heq
    subst heq
    simp [MyNat.add, MyNat.add_comm_succ_left] at hk
    exact absurd hk (MyNat.no_overflow m (k.succ))

theorem MyNat.lt_succ {n m : MyNat} (h : n.lt m) : n.lt m.succ := by
  obtain ⟨⟨k, hk⟩, hne⟩ := h
  -- hk : n + k = m,  hne : n ≠ m
  -- Since n ≠ m and n + k = m, k must be a successor
  cases k with
  | zero =>
    -- k = 0 means n = m, contradicts hne
    simp [MyNat.add] at hk
    exact absurd hk hne
  | succ k =>
    -- k = k'.succ, so n + k'.succ = m
    -- witness for n.lt m.succ is k.succ.succ
    constructor
    · -- n ≤ m.succ: witness is k.succ.succ
      refine ⟨k.succ.succ, ?_⟩
      simp [MyNat.add] at hk ⊢
      exact hk
    · -- n ≠ m.succ
      intro heq
      -- heq : n = m.succ, hk : n + k.succ = m
      -- substituting: m.succ + k.succ = m, impossible
      subst heq
      simp [MyNat.add, MyNat.add_comm_succ_left] at hk
      -- hk now says m.succ + k.succ = m, i.e. (m + k).succ.succ = m
      exact absurd hk (MyNat.no_overflow m (k.succ))

theorem MyNat.succ_le_succ {n m : MyNat} (h : n ≤ m) : n.succ ≤ m.succ := by
  simp_all
  obtain ⟨k, hk⟩ := h
  refine ⟨k, ?_⟩
  subst hk
  apply MyNat.add_comm_succ_left

theorem MyNat.lt_succ_mp {n m : MyNat} : n.lt m.succ → n.le m := by
  intro h
  simp_all [MyNat.le, MyNat.lt]
  obtain ⟨hl, hr⟩ := h
  obtain ⟨k, hk⟩ := hl
  cases k
  · simp [MyNat.add] at hk; contradiction
  · rename_i k
    refine ⟨k, ?_⟩
    simpa [MyNat.add] using hk

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
    rcases MyNat.lt_or_eq_of_le hk with hlt | rfl
    · have := MyNat.lt_succ_mp hlt
      exact ih k this
    · refine step n.succ (fun j hj => ?_)
      have := MyNat.lt_succ_mp hj
      exact ih j this

theorem MyNat.succ_ne_self (n : MyNat) : n.succ ≠ n := by
  induction n with
  | zero      => simp
  | succ n ih => intro h; have := MyNat.succ.inj h; exact ih this

theorem MyNat.succ_le_of_lt {n m : MyNat} (h : n < m) : n.succ ≤ m := by
  obtain ⟨⟨k, hk⟩, hne⟩ := h
  cases k with
  | zero      => simp [MyNat.add] at hk; exact absurd hk hne
  | succ k    =>
    exact ⟨k, by simp [MyNat.add] at hk ⊢; subst hk; apply MyNat.add_comm_succ_left⟩

theorem MyNat.lt_or_ge (n m : MyNat) : n < m ∨ n ≥ m := by
  induction m with
  | zero      => exact Or.inr (MyNat.zero_le n)
  | succ m ih =>
    rcases ih with hlt | hge
    · exact Or.inl (MyNat.lt_succ hlt)
    · rcases MyNat.lt_or_eq_of_le hge with hlt | rfl
      · -- m < n, so m.succ ≤ n, so n ≥ m.succ
        exact Or.inr (MyNat.succ_le_of_lt hlt)
      · -- n = m, so n < n.succ = m.succ
        exact Or.inl ⟨MyNat.le_succ hge, (MyNat.succ_ne_self m).symm⟩

theorem MyNat.lt_of_not_le : ∀ {a b : MyNat}, ¬(a.le b) → b.lt a := by
  intro a b hn
  exact (MyNat.lt_or_ge b a).resolve_right hn

theorem MyNat.well_ordering (S : MyNat → Prop) (hne : ∃ n, S n) :
    ∃ m, S m ∧ ∀ k, S k → m ≤ k := by
  obtain ⟨n, hn⟩ := hne
  -- For each n in S, either it's minimal or there's a smaller element.
  -- Strong induction finds the minimum by descending.
  apply MyNat.strong_ind (fun n => S n → ∃ m, S m ∧ ∀ k, S k → m ≤ k)
  · intro n ih hSn
    -- Is n already minimal?
    rcases Classical.em (∀ k, S k → n ≤ k) with hmin | hnotmin
    · exact ⟨n, hSn, hmin⟩
    · -- Some k < n is in S; ih gives a minimum below k, hence below n
      rw [Classical.not_forall] at hnotmin
      obtain ⟨k, hk⟩ := hnotmin
      rw [Classical.not_imp] at hk
      obtain ⟨hSk, hkn⟩ := hk
      exact ih k (MyNat.lt_of_not_le (by change ¬n.le k; exact hkn)) hSk
  · exact hn
