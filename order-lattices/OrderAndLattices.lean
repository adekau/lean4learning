-- a relationship is a subset  R ⊆ A × A.
def Rel (α : Type) : Type := α → α → Prop

-- a R a
def Reflexive {α : Type} (r : Rel α) : Prop :=
  ∀ (a : α), r a a

-- a R b implies b R a
def Symmetric {α : Type} (r : Rel α) : Prop :=
  ∀ (a b : α), r a b → r b a

-- a R b and b R a implies a = b
def Antisymm {α : Type} (r : Rel α) : Prop :=
  ∀ (a b : α), r a b → r b a → a = b

-- if a R b and b R c, then a R c
def Transitive {α : Type} (r : Rel α) : Prop :=
  ∀ (a b c : α), r a b → r b c → r a c

-- Partial Orders
-- Partial refers to the fact that not every 2 elements of α needs to be comparable
class PartialOrder (α : Type) [LE α] where
  le_refl               : ∀ (a : α), LE.le a a
  le_antisymm {a b : α} : LE.le a b → LE.le b a → a = b
  le_trans {a b c : α}  : LE.le a b → LE.le b c → LE.le a c

def lt {α : Type} [LE α] [PartialOrder α] (a b : α) : Prop :=
  LE.le a b ∧ ¬(a = b)

instance {α : Type} [LE α] [PartialOrder α] : LT α := ⟨lt⟩

instance : PartialOrder Nat where
  le_refl := Nat.le_refl
  le_antisymm := Nat.le_antisymm
  le_trans := Nat.le_trans

structure DvdNat where
  val : Nat
  deriving Repr, DecidableEq

instance : Coe DvdNat Nat := ⟨DvdNat.val⟩
instance : Coe Nat DvdNat := ⟨DvdNat.mk⟩
instance {n : Nat} : OfNat DvdNat n := ⟨⟨n⟩⟩

-- if n ∣ m, then there's a multiple of `n`, `k`, that makes `m`.
def Dvd' (n m : DvdNat) : Prop := ∃ k, m.val = n.val * k

instance : LE DvdNat := ⟨Dvd'⟩

-- if 0 ∣ m, then m = 0
theorem dvd_zero_left (m : DvdNat) (h : Dvd' 0 m) : m.val = 0 := by
  obtain ⟨k, hk⟩ := h
  have h0 : (0 : DvdNat).val = 0 := rfl
  rw [h0, Nat.zero_mul] at hk
  exact hk

--  if 𝑘 ⋅ 𝑗 = 1 in ℕ, then 𝑘 = 1
theorem mul_eq_one_left {k j : Nat} (h : k * j = 1) : k = 1 := by
  match k with
    | 0 =>
      rw [Nat.zero_mul] at h
      exact h
    | 1 => rfl
    | k + 2 =>
      exfalso
      have hj : j ≥ 1 := by
        cases j with
          | zero => simp only [Nat.mul_zero, Nat.zero_ne_one] at h
          | succ j =>
            have t := Nat.zero_le j
            exact Nat.succ_le_succ t
      have hbig : 2 ≤ (k + 2) * j :=
        calc 2 ≤ k + 2              := Nat.le_add_left 2 k
          k + 2 = (k + 2) * 1       := (Nat.mul_one (k + 2)).symm
          (k + 2) * 1 ≤ (k + 2) * j := Nat.mul_le_mul_left (k + 2) hj
      omega

theorem mul_eq_one_right {k j : Nat} (h : k * j = 1) : j = 1 := by
  have opp : j * k = 1 := by
    rw [Nat.mul_comm] at h
    exact h
  exact mul_eq_one_left opp

--  if 𝑎 > 0, 𝑎 ∣ 𝑏, and 𝑏 ∣ 𝑎, then 𝑎 = 𝑏.
theorem dvd_antisymm_pos
    {a b : Nat} (ha : 0 < a)
    (k : Nat) (hk : b = a * k)
    (j : Nat) (hj : a = b * j) : a = b := by
  have hkj : k * j = 1 := by
    have hstep : a = a * (k * j) :=
      calc a = b * j        := hj
           _ = (a * k) * j  := by rw [hk]
           _ = a * (k * j)  := by rw [Nat.mul_assoc]
    exact Nat.eq_of_mul_eq_mul_left ha (by rw [Nat.mul_one]; exact hstep.symm)
  have h : j = 1      := mul_eq_one_right hkj
  have h₂ : a = b * 1 := by rw [h] at hj; exact hj
  have h₃ : a = b     := by rw [Nat.mul_one] at h₂; exact h₂
  exact h₃

instance : PartialOrder DvdNat where
  le_refl {n}         := ⟨1, by rw [Nat.mul_one]⟩
  le_antisymm {n m}   := fun k j => by
    -- not shadowing because obtain destructs
    obtain ⟨k, hk⟩ := k
    obtain ⟨j, hj⟩ := j
    cases n; cases m
    congr 1
    rename_i a b
    cases Nat.eq_zero_or_pos a with
      | inl ha =>
        subst ha
        have h : Dvd' 0 b := ⟨k, hk⟩
        exact (dvd_zero_left ⟨b⟩ h).symm
      | inr ha =>
        exact dvd_antisymm_pos ha k hk j hj
  le_trans {n m q}    := fun ⟨k, hk⟩ ⟨j, hj⟩ =>
    ⟨k * j, by rw [hj, hk, Nat.mul_assoc]⟩

example : DvdNat.mk 5 ≤ DvdNat.mk 10 :=
  @Exists.intro
    Nat (fun k => 10 = 5 * k)
    2 rfl

example : ¬ (DvdNat.mk 3 ≤ DvdNat.mk 10) := by
  intro ⟨k, hk⟩
  -- hk : 10 = 3 * k
  -- We case split on k and rule out every possibility.
  match k with
  | 0 => simp [Nat.mul_zero] at hk   -- 10 = 0, absurd
  | 1 => simp [Nat.mul_one]  at hk   -- 10 = 3, absurd
  | 2 => exact absurd hk (by decide) -- 10 = 6, absurd
  | 3 => exact absurd hk (by decide) -- 10 = 9, absurd
  | k + 4 =>
    have hge : 3 * (k + 4) ≥ 12 :=
      calc 3 * (k + 4) = 3 * k + 12 := by rw [Nat.mul_add]
                     _ ≥ 12          := Nat.le_add_left 12 (3 * k)
    -- hk : {val:=10}.val = {val:=3}.val * (k+4)
    -- simplify .val accesses to bare Nats first
    have hk' : 10 = 3 * (k + 4) := hk
    -- now substitute: 10 = 3*(k+4) and 3*(k+4) ≥ 12, so 10 ≥ 12
    have : 10 ≥ 12 := hk' ▸ hge
    exact absurd this (by decide)

def Set (α : Type) : Type := α → Prop

def Set.subset {α : Type} (s t : Set α) : Prop :=
  ∀ (a : α), s a → t a

instance {α : Type} : LE (Set α) where
  le := Set.subset

instance {α : Type} : PartialOrder (Set α) where
  le_refl {_ _}       := id
  le_antisymm {s t}   := fun h₁ h₂ => by
    have h : ∀ (a : α), s a = t a := fun a => propext ⟨h₁ a, h₂ a⟩
    exact funext h
  le_trans {_ _ _}    := fun h1 h2 a ha => by
    have e₁ := h1 a ha
    have e₂ := h2 a e₁
    exact e₂

-- The set of even numbers
def evens : Set Nat := fun n => ∃ k, n = 2 * k

example : evens 6 := ⟨3, rfl⟩

example : ¬ evens 3 := by
  intro ⟨k, hk⟩
  match k with
    | 0 | 1 => exact absurd hk (by decide)
    | k + 2 =>
      have hge : 4 ≤ 2 * (k + 2) :=
        calc 2 * (k + 2) = 2 * k + 4 := by rw [Nat.mul_add]
                       _ ≥ 4         := Nat.le_add_left 4 (2 * k)
      have : 3 ≥ 4 := hk ▸ hge
      exact absurd this (by decide)

def IsTop {α : Type} [LE α] [PartialOrder α] (t : α) : Prop :=
  ∀ a : α, a ≤ t

def IsBot {α : Type} [LE α] [PartialOrder α] (b : α) : Prop :=
  ∀ a : α, b ≤ a

def IsMaximum {α : Type} [LE α] [PartialOrder α] (s : Set α) (t : α) : Prop :=
  s t ∧ (∀ a : α, s a → a ≤ t)

def IsMinimum {α : Type} [LE α] [PartialOrder α] (s : Set α) (b : α) : Prop :=
  s b ∧ (∀ a : α, s a → b ≤ a)

class Bot (α : Type) [LE α] where
  bot : α
  bot_le : ∀ (a : α), bot ≤ a

class Top (α : Type) [LE α] where
  top : α
  top_le : ∀ (a : α), a ≤ top

class Bounded (α : Type) [LE α] [PartialOrder α] extends Bot α, Top α

notation "⊥" => Bot.bot
notation "⊤" => Top.top

#eval (5 : Fin 12) ≤ (6 : Fin 12)

instance (n : Nat) : PartialOrder (Fin n) where
  le_refl := Fin.le_refl
  le_antisymm := Fin.le_antisymm
  le_trans := Fin.le_trans

instance : Bounded (Fin 12) where
  top := 11
  bot := 0
  bot_le := Fin.zero_le
  top_le := Fin.le_last

-- 2.2 Upper/Lower bounds

-- supremum, the smallest upper bound of a pair of elements in a relation
structure IsSupOf {α : Type} [LE α] [PartialOrder α] (a b sup : α) : Prop where
  -- sup bigger than element a
  ge_a : a ≤ sup
  -- sup bigger than element b
  ge_b : b ≤ sup
  -- for all u bigger than both a and b, returns a proof of the suprenum being less than u
  least : ∀ (u : α), a ≤ u → b ≤ u → sup ≤ u

-- infimum, the greatest lower bound of a pair of elements in a relation
structure IsInfOf {α : Type} [LE α] [PartialOrder α] (a b inf : α) : Prop where
  -- inf is less than element a
  le_a : inf ≤ a
  -- inf is less than element b
  le_b : inf ≤ b
  -- for all u smaller than both a and b, returns a proof of the infimum being greater than u
  greatest : ∀ (u : α), u ≤ a → u ≤ b → u ≤ inf

-- if a supremum exists, it's unique.
theorem sup_unique {α : Type} [LE α] [PartialOrder α]
    {a b s t : α}
    (hs : IsSupOf a b s) (ht : IsSupOf a b t) : s = t := by
  -- apply antisymm (s ≤ t → t ≤ s → s = t) to the goal.
  -- transforms it into cases for providing both the arguments (`s ≤ t` and `t ≤ s`)
  apply PartialOrder.le_antisymm
  · exact hs.least t ht.ge_a ht.ge_b
  · exact ht.least s hs.ge_a hs.ge_b

-- if a infimum exists, it's unique.
theorem inf_unique {α : Type} [LE α] [PartialOrder α]
    {a b s t : α}
    (hs : IsInfOf a b s) (ht : IsInfOf a b t) : s = t := by
  apply PartialOrder.le_antisymm
  · exact ht.greatest s hs.le_a hs.le_b
  · exact hs.greatest t ht.le_a ht.le_b

-- 2.3 Monotone Maps

-- A function 𝑓 ∶ (𝑃 , ≤_𝑃) → (𝑄, ≤_𝑄) between posets is monotone (or orderpreserving) if ∀𝑎, 𝑏 ∈ 𝑃 , 𝑎 ≤𝑃 𝑏 → 𝑓(𝑎) ≤𝑄 𝑓(𝑏).
structure Monotone {α β : Type}
    [LE α] [LE β] [PartialOrder α] [PartialOrder β]
    (f : α → β) : Prop where
  -- A proof that for all a less than b, applying 𝑓 does not change that relation.
  map_le : ∀ (a b : α), a ≤ b → f a ≤ f b

theorem Monotone.comp {α β γ : Type}
    [LE α] [LE β] [LE γ] [PartialOrder α] [PartialOrder β] [PartialOrder γ]
    {f : α → β} {g : β → γ}
    (hf : Monotone f) (hg : Monotone g) : Monotone (g ∘ f) where
  map_le := fun a b h => by
    have h₁ := (hf.map_le a b h)
    exact hg.map_le (f a) (f b) h₁

structure Antitone {α β : Type}
    [LE α] [LE β] [PartialOrder α] [PartialOrder β]
    (f : α → β) : Prop where
  -- reverses order
  map_le : ∀ (a b : α), a ≤ b → f b ≤ f a

theorem Antitone.comp {α β γ : Type}
    [LE α] [LE β] [LE γ] [PartialOrder α] [PartialOrder β] [PartialOrder γ]
    {f : α → β} {g : β → γ}
    (hf : Antitone f) (hg : Antitone g) : Monotone (g ∘ f) where
  map_le := fun a b h => by
    have h₁ := (hf.map_le a b h)
    exact hg.map_le (f b) (f a) h₁

-- A fixed point is a point in a set unaffected by a mapping function.
structure IsFixedPoint {α : Type} {f : α → α} (x : α) : Prop where
  fp : f x = x

-- define multiple function application `n` times, 𝑓ⁿ x
def iter {α : Type} (f : α → α) : Nat → α → α
  | 0, x      => x                -- f⁰ x is just x, don't apply the function
  | n + 1, x  => f (iter f n x)   -- fⁿ⁺¹ x = f (fⁿ x)

-- for monotone 𝑓, if 𝑎 ≤ 𝑓 𝑎, then the repeated application of 𝑓 ascends:
-- 𝑎 ≤ 𝑓 𝑎 ≤ 𝑓² 𝑎 ≤ ⋯
theorem fixed_point_chain {α : Type} {f : α → α} {a : α}
    [LE α] [PartialOrder α]
    (hf : Monotone f) (ha : a ≤ f a) :
    ∀ (n : Nat), iter f n a ≤ iter f (n + 1) a := by
  intro n
  induction n with
    | zero      =>
      exact ha
    | succ n ih =>
      let arg₁ := iter f n a
      let arg₂ := iter f (n + 1) a
      exact hf.map_le arg₁ arg₂ ih

-- (id : 𝑎 → 𝑎) is monotone since a ≤ b → id a ≤ id b by hypothesis (a ≤ b)
theorem Monotone.id {α : Type} [LE α] [PartialOrder α] :
    -- type annotation so that Monotone's implicit α resolves to α, and β resolves to α.
    -- can also do `@id α`, or `Monotone (β := α) id`
    Monotone (id : α → α) where
  map_le := fun _ _ h => h

-- 3 Lattices
-- 3.1 Meet and join

-- A lattice is a poset in which every pair of elements has a supremum and infimum.
-- Meet: Greatest lower bound, `a ⊓ b`.
-- Join: Least upper bound, `a ⊔ b`.
class Lattice (α : Type) extends LE α, PartialOrder α where
  inf           : α → α → α -- meet, ⊓
  sup           : α → α → α -- join, ⊔
  -- meet is lower bound
  inf_le_left   : ∀ (a b : α), inf a b ≤ a
  inf_le_right  : ∀ (a b : α), inf a b ≤ b
  le_inf        : ∀ (a b c : α), a ≤ b → a ≤ c → a ≤ inf b c
  -- join is upper bound
  sup_le_left   : ∀ (a b : α), a ≤ sup a b
  sup_le_right  : ∀ (a b : α), b ≤ sup a b
  le_sup        : ∀ (a b c : α), a ≤ c → b ≤ c → sup a b ≤ c

-- Lattice notation
infixl:70 " ⊓ " => Lattice.inf
infixl:65 " ⊔ " => Lattice.sup

theorem inf_comm {α : Type} [Lattice α] {a b : α} :
    a ⊓ b = b ⊓ a := by
  apply PartialOrder.le_antisymm
  · apply Lattice.le_inf
    · apply Lattice.inf_le_right
    · apply Lattice.inf_le_left
  · apply Lattice.le_inf
    · apply Lattice.inf_le_right
    · apply Lattice.inf_le_left

-- 3.2 Duality
structure Dual (α : Type) where
  val : α

theorem Dual.mk_inj {α : Type} {a b : α} :
    (⟨a⟩ : Dual α) = ⟨b⟩ ↔ a = b := by
  constructor
  · exact congrArg Dual.val
  · exact congrArg Dual.mk

instance {α : Type} [Lattice α] : Lattice (Dual α) where
  le a b                  := LE.le (α := α) b.val a.val   -- a ≤_dual b means b ≤_original a
  le_refl {a}             := PartialOrder.le_refl a.val
  le_antisymm {_ _ h1 h2} := congrArg Dual.mk (PartialOrder.le_antisymm (α := α) h2 h1)
  le_trans {_ _ _ h1 h2}  := PartialOrder.le_trans (α := α) h2 h1
  inf {a b}               := ⟨Lattice.sup a.val b.val⟩
  sup {a b}               := ⟨Lattice.inf a.val b.val⟩
  inf_le_left {a b}       := Lattice.sup_le_left a.val b.val
  inf_le_right {a b}      := Lattice.sup_le_right a.val b.val
  sup_le_left {a b}       := Lattice.inf_le_left a.val b.val
  sup_le_right {a b}      := Lattice.inf_le_right a.val b.val
  le_inf {a b c h1 h2}    := Lattice.le_sup b.val c.val a.val h1 h2
  le_sup {a b c h1 h2}    := Lattice.le_inf c.val a.val b.val h1 h2

theorem sup_comm {α : Type} [Lattice α] {a b : α} :
    a ⊔ b = b ⊔ a := by
  have h := @inf_comm (Dual α) _ ⟨a⟩ ⟨b⟩
  rwa [Dual.mk_inj] at h

theorem inf_assoc {α : Type} [Lattice α] {a b c : α} :
    a ⊓ (b ⊓ c) = (a ⊓ b) ⊓ c := by
  apply PartialOrder.le_antisymm
  · apply Lattice.le_inf
    · apply Lattice.le_inf
      · exact Lattice.inf_le_left a (b ⊓ c)
      · have h₁ := Lattice.inf_le_right a (b ⊓ c)
        have h₂ := Lattice.inf_le_left b c
        exact PartialOrder.le_trans h₁ h₂
    · have h₁ := Lattice.inf_le_right a (b ⊓ c)
      have h₂ := Lattice.inf_le_right b c
      exact PartialOrder.le_trans h₁ h₂
  · apply Lattice.le_inf
    · have h₁ : a ⊓ b ⊓ c ≤ a ⊓ b := Lattice.inf_le_left (a ⊓ b) c
      have h₂ : a ⊓ b ≤ a := Lattice.inf_le_left a b
      exact PartialOrder.le_trans h₁ h₂
    · apply Lattice.le_inf
      · have h₁ := Lattice.inf_le_left (a ⊓ b) c
        have h₂ := Lattice.inf_le_right a b
        exact PartialOrder.le_trans h₁ h₂
      · exact Lattice.inf_le_right (a ⊓ b) c

theorem sup_assoc {α : Type} [Lattice α] {a b c : α} :
    a ⊔ (b ⊔ c) = (a ⊔ b) ⊔ c := by
  have h := @inf_assoc (Dual α) _ ⟨a⟩ ⟨b⟩ ⟨c⟩
  rwa [Dual.mk_inj] at h

theorem inf_idempotent {α : Type} [Lattice α] {a : α} :
    a ⊓ a = a := by
  apply PartialOrder.le_antisymm
  · exact Lattice.inf_le_left a a
  · apply Lattice.le_inf
    · apply PartialOrder.le_refl
    · apply PartialOrder.le_refl

theorem sup_idempotent {α : Type} [Lattice α] {a : α} :
    a ⊔ a = a := by
  have h := @inf_idempotent (Dual α) _ ⟨a⟩
  rwa [Dual.mk_inj] at h

theorem sup_absorbtion {α : Type} [Lattice α] {a b : α} :
    a ⊔ (a ⊓ b) = a := by
  apply PartialOrder.le_antisymm
  · apply Lattice.le_sup
    · apply PartialOrder.le_refl
    · apply Lattice.inf_le_left
  · apply Lattice.sup_le_left

theorem inf_absorbtion {α : Type} [Lattice α] {a b : α} :
    a ⊓ (a ⊔ b) = a := by
  have h := @sup_absorbtion (Dual α) _ ⟨a⟩ ⟨b⟩
  rwa [Dual.mk_inj] at h

instance : Lattice Bool where
  le            := (· ≤ ·)
  le_refl       := Bool.le_refl
  le_antisymm   := Bool.le_antisymm
  le_trans      := Bool.le_trans
  inf           := (· && ·)
  sup           := (· || ·)
  inf_le_left   := by decide
  inf_le_right  := by decide
  le_inf        := by decide
  sup_le_left   := by decide
  sup_le_right  := by decide
  le_sup        := by decide

def Set.inter {α : Type} (s t : Set α) : Set α := fun a => s a ∧ t a
def Set.union {α : Type} (s t : Set α) : Set α := fun a => s a ∨ t a

instance {α : Type} : Lattice (Set α) where
  le                  := Set.subset
  le_refl             := fun s a ha => ha
  le_antisymm {a b}   := fun h₁ h₂ => funext (fun a => propext ⟨h₁ a, h₂ a⟩)
  le_trans {a b c}    := fun h₁ h₂ a ha => by
    have t₁ := h₁ a ha
    have t₂ := h₂ a t₁
    exact t₂
  inf                 := Set.inter
  sup                 := Set.union
  le_inf              := fun s t u ab ac a ha => by
    exact ⟨ab a ha, ac a ha⟩
  inf_le_left         := fun s t a ht => ht.left
  inf_le_right        := fun s t a ⟨htl, htr⟩ => htr
  le_sup              := fun s t u su tu a ht => ht.elim (su a) (tu a)
  sup_le_left         := fun s t a ha => Or.inl ha
  sup_le_right        := fun s t a ha => Or.inr ha

instance : Lattice Nat where
  le                  := (· ∣ ·)
  le_refl             := fun a => by exact ⟨1, by omega⟩
  le_antisymm         := Nat.dvd_antisymm
  le_trans            := Nat.dvd_trans
  inf                 := Nat.gcd
  sup                 := Nat.lcm
  inf_le_left         := Nat.gcd_dvd_left
  inf_le_right        := Nat.gcd_dvd_right
  le_inf              := fun a b c => Nat.dvd_gcd
  sup_le_left         := Nat.dvd_lcm_left
  sup_le_right        := Nat.dvd_lcm_right
  le_sup              := fun a b c ha hb => Nat.lcm_dvd ha hb

structure Interval where
  -- interval lower bound
  l       : Int
  -- interval upper bound
  h       : Int
  -- proof that the lower bound is LE upper bound
  l_le_h  : l ≤ h

instance : LE Interval where
  -- containment by smaller interval
  -- int₁ ≤ int₂ ↔ l₂ ≤ l₁ ∧ h₁ ≤ h₂
  -- [l₁, h₁] ≤ [l₂, h₂] ↔ l₂ ≤ l₁ ∧ h₁ ≤ h₂
  -- So left hand side interval should be contained within the right hand side interval, AKA more specific.
  le := fun int₁ int₂ => (int₂.l ≤ int₁.l) ∧ (int₁.h ≤ int₂.h)

instance : PartialOrder Interval where
  le_refl           := fun a => by
    have l₂_le_l₁ := show a.l ≤ a.l from Int.le_refl a.l
    have h₁_le_h₂ := show a.h ≤ a.h from Int.le_refl a.h
    exact ⟨l₂_le_l₁, h₁_le_h₂⟩
  le_antisymm {a b} := fun hyp₁ hyp₂ => by
    -- a ≤ b says: (b.l ≤ a.l) ∧ (a.h ≤ b.h)
    -- b ≤ a says: (a.l ≤ b.l) ∧ (b.h ≤ a.h)
    cases a; cases b;
    rename_i l₁ h₁ l₁_le_h₁ l₂ h₂ l₂_le_h₂
    congr 1
    · exact Int.le_antisymm hyp₂.left hyp₁.left
    · exact Int.le_antisymm hyp₁.right hyp₂.right
      -- Don't need to show l₁_le_h₁ = l₂_le_h₂ by `proof_irrel` axiom
  le_trans {a b c}  := fun hyp₁ hyp₂ => by
    rcases a with ⟨a_l, a_h, a_le⟩
    rcases b with ⟨b_l, b_h, b_le⟩
    rcases c with ⟨c_l, c_h, c_le⟩
    simp [LE.le] at *
    -- now we can traverse the transitive property of each field using le_trans on Int
    -- if we want to say a ≤ c, then we need 2 proofs:
    -- c_l ≤ a_l
    -- a_h ≤ c_h
    have hl_ba : b_l ≤ a_l := hyp₁.left
    have hl_cb : c_l ≤ b_l := hyp₂.left
    have hl_ca : c_l ≤ a_l := Int.le_trans hl_cb hl_ba
    have hh_ab : a_h ≤ b_h := hyp₁.right
    have hh_bc : b_h ≤ c_h := hyp₂.right
    have hh_ac : a_h ≤ c_h := Int.le_trans hh_ab hh_bc
    exact ⟨hl_ca, hh_ac⟩

instance {α β : Type} [Lattice α] [Lattice β] : Lattice (α × β) where
  le                := fun a b => (a.fst ≤ b.fst) ∧ (a.snd ≤ b.snd)
  le_refl           := fun a => by
    apply And.intro
    · apply PartialOrder.le_refl
    · apply PartialOrder.le_refl
  le_antisymm {a b} := fun hyp₁ hyp₂ => by
    rcases a with ⟨l₁, r₁⟩
    rcases b with ⟨l₂, r₂⟩
    congr 1
    · exact PartialOrder.le_antisymm hyp₁.left hyp₂.left
    · exact PartialOrder.le_antisymm hyp₁.right hyp₂.right
  le_trans {a b c}  := fun hyp₁ hyp₂ => by
    apply And.intro
    · exact PartialOrder.le_trans hyp₁.left hyp₂.left
    · exact PartialOrder.le_trans hyp₁.right hyp₂.right
  inf := fun a b =>
    ⟨Lattice.inf a.fst b.fst, Lattice.inf a.snd b.snd⟩
  sup := fun a b =>
    ⟨Lattice.sup a.fst b.fst, Lattice.sup a.snd b.snd⟩
  inf_le_left       := fun a b => by
    apply And.intro
    · apply Lattice.inf_le_left
    · apply Lattice.inf_le_left
  inf_le_right      := fun a b => by
    apply And.intro
    · apply Lattice.inf_le_right
    · apply Lattice.inf_le_right
  le_inf            := fun a b c hyp₁ hyp₂ => by
    apply And.intro
    · apply Lattice.le_inf
      · exact hyp₁.left
      · exact hyp₂.left
    · apply Lattice.le_inf
      · exact hyp₁.right
      · exact hyp₂.right
  sup_le_left       := fun a b => by
    apply And.intro
    · apply Lattice.sup_le_left
    · apply Lattice.sup_le_left
  sup_le_right      := fun a b => by
    apply And.intro
    · apply Lattice.sup_le_right
    · apply Lattice.sup_le_right
  le_sup            := fun a b c hyp₁ hyp₂ => by
    apply And.intro
    · apply Lattice.le_sup
      · exact hyp₁.left
      · exact hyp₂.left
    · apply Lattice.le_sup
      · exact hyp₁.right
      · exact hyp₂.right

theorem le_iff_sup_eq {α : Type} [Lattice α] {a b : α} :
    a ≤ b ↔ a ⊔ b = b := by
  apply Iff.intro
  · intro h
    apply PartialOrder.le_antisymm
    · apply Lattice.le_sup
      · exact h
      · exact PartialOrder.le_refl b
    · exact Lattice.sup_le_right a b
  · intro h
    rw [← h]
    exact Lattice.sup_le_left a b

def Pred (α : Type) := α → Prop

-- A lattice (𝐿, ≤) is complete if every subset 𝑆 ⊆ 𝐿 has a supremum `⋁ 𝑆` and an infimum `⋀ 𝑆` in
class CompleteLattice (α : Type) extends Lattice α where
  sSup : Pred α → α -- supremum of a set
  sInf : Pred α → α -- infimum of a set
  -- Says that sSup is an upper bound. Every element of set s, a, is less than sSup s.
  le_sSup : ∀ (s : Pred α) (a : α), s a → a ≤ sSup s
  -- (∀ a : α, s a → a ≤ u) → sSup s ≤ u says:
  -- for all elements in set s, a ≤ u where u is an upper bound.
  -- Then, a proof of this implies that the supremum of the set, s, is less than or equal to any upper bound
  -- Says that sSup s is the _least_ upper bound.
  sSup_le : ∀ (s : Pred α) (u : α), (∀ a : α, s a → a ≤ u) → sSup s ≤ u
  -- equivalent of the sSup le statements but for greatest lower bound
  sInf_le : ∀ (s : Pred α) (a : α), s a → sInf s ≤ a
  le_sInf : ∀ (s : Pred α) (l : α), (∀ a : α, s a → l ≤ a) → l ≤ sInf s

-- Powerset lattice, ⋁ ℱ = ⋃ ℱ and ⋀ ℱ = ⋂ ℱ
instance {α : Type} : CompleteLattice (Set α) where
  -- F is a family of sets matching the predicate
  -- a is an element of the lattice
  -- There exists a set such that the set is in the family of sets and `a` is an element of the set
  -- Union of the sets in the family
  -- Concretely, say F is the family { {1,2}, {2,3}, {3,4} }. Then:
  -- Union ⋃ F = {1,2} ∪ {2,3} ∪ {3,4} = {1,2,3,4}
  sSup := fun F a => ∃ s : Set α, F s ∧ s a
  -- F is a family of sets matching the predicate
  -- a is an element of the lattice
  -- `a` is an element of every set in the family.
  -- Intersection of the sets in the family
  -- ⋂ F = {1,2} ∩ {2,3} ∩ {3,4} = {}
  sInf := fun F a => ∀ s : Set α, F s → s a
  le_sSup := fun _ s hs _ ha =>
    ⟨s, ⟨hs, ha⟩⟩
  sSup_le := fun _ _ hu a ⟨s, hs, ha⟩ => hu s hs a ha
  le_sInf := fun _ _ hl a ha s hs => hl s hs a ha
  sInf_le := fun _ s hs _ ha => ha s hs

theorem knaster_tarski {α : Type} [CompleteLattice α]
  (f : α → α) (hf : Monotone f) :
    -- There's a least fixed point such that when a monotone map is applied to it, it equals itself
    -- and for all x in the lattice where the monotone map `f` applied to `x` results in x (fixed point),
    -- the least fixed point (`lfp`) is less than or equal to it.
    ∃ (lfp : α), f lfp = lfp ∧
    ∀ (x : α), f x = x → lfp ≤ x := by
  let P : Pred α := fun x => f x ≤ x
  let m := CompleteLattice.sInf P
  -- Step 1 : f(m) ≤ m
  have step1 : f m ≤ m := by
    apply CompleteLattice.le_sInf
    intro x hx
    simp only [P] at *
    have hh := hf.map_le m x (CompleteLattice.sInf_le P x hx)
    exact PartialOrder.le_trans hh hx
  have step2 : m ≤ f m := by
    apply CompleteLattice.sInf_le
    simp [P]
    exact hf.map_le (f m) m step1
  have fixed : f m = m := PartialOrder.le_antisymm step1 step2
  refine ⟨m, fixed, ?_⟩
  -- Minimality
  intro x hx
  apply CompleteLattice.sInf_le
  simp only [P, hx]
  exact PartialOrder.le_refl x

class BoundedJoinSemilattice (α : Type) extends LE α, PartialOrder α where
  sup : α → α → α
  bot : α
  le_sup_left   : ∀ (a b : α), a ≤ sup a b
  le_sup_right  : ∀ (a b : α), b ≤ sup a b
  sup_le        : ∀ (a b c : α), a ≤ c → b ≤ c → sup a b ≤ c
  bot_le        : ∀ (a : α), bot ≤ a

infixl:65 " ⊔ " => BoundedJoinSemilattice.sup
notation  "⊥"   => BoundedJoinSemilattice.bot

structure Propagator1 (α β : Type)
  [BoundedJoinSemilattice α] [BoundedJoinSemilattice β] where
  fn        : α → β
  monotone  : ∀ (a b : α), a ≤ b → fn a ≤ fn b

structure Propagator2 (α β γ : Type)
  [BoundedJoinSemilattice α] [BoundedJoinSemilattice β] [BoundedJoinSemilattice γ] where
  fn        : α → β → γ
  monotone  : ∀ (a₁ a₂ : α) (b₁ b₂ : β),
    a₁ ≤ a₂ → b₁ ≤ b₂ → fn a₁ b₁ ≤ fn a₂ b₂

structure Cell (α : Type) where
  ref : IO.Ref α

def Cell.new {α} [BoundedJoinSemilattice α] [DecidableEq α] : IO (Cell α) := do
  let r ← IO.mkRef (BoundedJoinSemilattice.bot (α := α))
  return { ref := r }

def Cell.read {α} [BoundedJoinSemilattice α] [DecidableEq α] (c : Cell α) : IO α :=
  c.ref.get

def Cell.write {α} [BoundedJoinSemilattice α] [DecidableEq α] (c : Cell α) (v : α) : IO Bool := do
  let old ← c.ref.get
  let merged := old ⊔ v
  if merged == old then
    return false
  else
    c.ref.set merged
    return true

abbrev PropStep := IO Bool

def runToFixpoint (steps : Array PropStep) : IO Unit := do
  let mut changed := true
  while changed do
    changed := false
    for step in steps do
      let c ← step
      if c then changed := true

structure Network where
  steps : Array PropStep

def Network.run (n : Network) : IO Unit :=
  runToFixpoint n.steps

inductive FlatNat where
  | unknown         : FlatNat
  | known (n : Nat) : FlatNat
  | conflict        : FlatNat
  deriving Repr, DecidableEq

instance : ToString FlatNat where
  toString a := match a with
    | .unknown  => "unknown"
    | .known n  => ToString.toString n
    | .conflict => "conflict"

def FlatNat.le (a b : FlatNat) : Prop :=
  match a, b with
    | .unknown , _         => True
    | _        , .conflict => True
    | .known m , .known n  => m = n
    | .conflict, .unknown  => False
    | .conflict, .known _  => False
    | .known _ , .unknown  => False

instance : LE FlatNat := ⟨FlatNat.le⟩

instance : PartialOrder FlatNat where
  le_refl       := by
    intro a
    cases a <;> trivial
    -- · simp only [LE.le]
    -- · rename_i n
    --   simp only [LE.le]
    -- · simp only [LE.le]
  le_antisymm   := by
    intro a b hab hba
    cases a <;> cases b <;> simp_all [LE.le, FlatNat.le]
  le_trans      := by
    intro a b c hab hbc
    cases a <;> cases b <;> cases c <;> simp_all [LE.le, FlatNat.le]

instance : BoundedJoinSemilattice FlatNat where
  bot         := .unknown
  sup a b     := match a, b with
    | .unknown, x         => x
    | x       , .unknown  => x
    | .known m, .known n  => if m = n then .known m else .conflict
    | _       , _         => .conflict
  bot_le      := by
    intro a
    cases a <;> simp [LE.le, FlatNat.le]
  le_sup_left := by
    intro a b
    cases a <;> cases b <;> simp_all [LE.le, FlatNat.le]
    rename_i m n
    by_cases h : m = n <;> simp [h]
  le_sup_right := by
    intro a b
    cases a <;> cases b <;> simp_all [LE.le, FlatNat.le]
    rename_i m n
    by_cases h : m = n <;> simp [h]
  sup_le      := by
    intro a b c hac hbc
    cases a <;> cases b <;> cases c <;> simp_all [LE.le, FlatNat.le]
    rename_i m n
    by_cases h : m = n <;> simp [h]

def FlatNat.add (x y : FlatNat) : FlatNat :=
  match x, y with
    | .known a  , .known b  => .known (a + b)
    | .conflict , _         => .conflict
    | _         , .conflict => .conflict
    | _         , _         => .unknown

def addPropagator : Propagator2 FlatNat FlatNat FlatNat where
  fn        := FlatNat.add
  monotone  := by
    intro a1 a2 b1 b2 ha hb
    cases a1 <;> cases a2 <;> cases b1 <;> cases b2
      <;> simp_all [FlatNat.add, FlatNat.le, LE.le]

def FlatNat.sub (total x : FlatNat) : FlatNat :=
  match total, x with
    | .known t  , .known a  =>
      if a ≤ t then .known (t - a)
               else .conflict
    | .conflict , _         => .conflict
    | _         , .conflict => .conflict
    | _         , _         => .unknown

def subPropagator : Propagator2 FlatNat FlatNat FlatNat where
  fn        := FlatNat.sub
  monotone := by
    intro a1 a2 b1 b2 ha hb
    simp only [FlatNat.le, LE.le] at ha hb ⊢
    cases a1 <;> cases a2 <;> cases b1 <;> cases b2
      <;> simp_all [FlatNat.sub]
      <;> split <;> simp_all

def addProp (cx cy csum : Cell FlatNat) : PropStep := do
  let cx ← cx.read
  let cy ← cy.read
  let sum := FlatNat.add cx cy
  csum.write sum

def subProp (ctotal cx cy : Cell FlatNat) : PropStep := do
  let total ← ctotal.read
  let x ← cx.read
  let diff := FlatNat.sub total x
  cy.write diff

def exampleNetwork : IO Unit := do
  let cx ← Cell.new (α := FlatNat)
  let cy ← Cell.new (α := FlatNat)
  let csum ← Cell.new (α := FlatNat)

  let _ ← cx.write (.known 3)
  let _ ← csum.write (.known 10)

  let net : Network := Network.mk #[
    addProp cx cy csum,
    subProp csum cx cy,
    subProp csum cy cx
  ]

  net.run

  let yVal ← cy.read
  IO.println s!"y is {yVal}"

#eval exampleNetwork

-- Exercise 6.1
def FlatNat.mul : FlatNat → FlatNat → FlatNat
  | .known a , .known b   => .known (a * b)
  | .conflict, _          => .conflict
  | _        , .conflict  => .conflict
  | _        , _          => .unknown

def mulPropagator : Propagator2 FlatNat FlatNat FlatNat where
  fn        := FlatNat.mul
  monotone  := by
    intro a1 a2 b1 b2 ha hb
    cases a1 <;> cases a2 <;> cases b1 <;> cases b2
    all_goals (simp_all [FlatNat.mul, FlatNat.le, LE.le])

def mulProp (cx cy cz : Cell FlatNat) : PropStep := do
  let x ← cx.read
  let y ← cy.read
  let prod := FlatNat.mul x y
  cz.write prod

def FlatNat.div : FlatNat → FlatNat → FlatNat
  | .known z  , .known x  =>
    if x ∣ z  then .known (z / x)
              else .conflict
  | .conflict , _         => .conflict
  | _         , .conflict => .conflict
  | _         , _         => .unknown

def divPropagator : Propagator2 FlatNat FlatNat FlatNat where
  fn        := FlatNat.div
  monotone  := by
    intro a1 a2 b1 b2 ha hb
    cases a1 <;> cases a2 <;> cases b1 <;> cases b2
    all_goals (simp_all [FlatNat.div, FlatNat.le, LE.le])
    · rename_i a1 a2 b1 b2
      by_cases h : b2 ∣ a2 <;> simp_all
    · split
      · exact True.intro
      · exact True.intro
      · contradiction
      · contradiction
      · contradiction
      · contradiction
    · split <;> trivial
    · split <;> trivial

def divProp (cz cx cy : Cell FlatNat) : PropStep := do
  let z ← cz.read
  let x ← cx.read
  let dvd := FlatNat.div z x
  cy.write dvd

def mulNetwork : IO Unit := do
  let cx ← Cell.new (α := FlatNat)
  let cy ← Cell.new (α := FlatNat)
  let cz ← Cell.new (α := FlatNat)

  let _ ← cx.write (.known 3)
  let _ ← cz.write (.known 12)

  let net : Network := Network.mk #[
    mulProp cx cy cz,
    divProp cz cx cy,
    divProp cz cy cx
  ]

  net.run

  let yVal ← cy.read
  IO.println s!"y is {yVal}"

#eval mulNetwork

namespace Ch7
inductive Interval where
  | empty                             : Interval
  | range (lo hi : Int) (h : lo ≤ hi) : Interval

def Interval.le (a b : Interval) : Prop :=
  match a, b with
    | .empty        , _               => True
    | .range _ _ _  , .empty          => False
    | .range l1 h1 _, .range l2 h2 _  => l2 ≤ l1 ∧ h1 ≤ h2

def Interval.sup (a b : Interval) : Interval :=
  match a, b with
    | .empty        , x               => x
    | x             , .empty          => x
    | .range l1 h1 _, .range l2 h2 _  =>
      let l := min l1 l2
      let h := max h1 h2
      .range l h (by omega)

instance : LE Interval := ⟨Interval.le⟩

instance : PartialOrder Interval where
  le_refl := by
    intro a
    cases a <;> simp [Interval.le, LE.le]
    apply And.intro
    all_goals (apply Int.le_refl)
  le_antisymm := by
    intro a b hab hba
    cases a <;> cases b
    · rfl
    · contradiction
    · contradiction
    · rename_i lo1 hi1 h1 lo2 hi2 h2
      simp only [Interval.le, LE.le] at hab hba
      have h_lo_eq : lo1 = lo2 := Int.le_antisymm hba.left hab.left
      have h_hi_eq : hi1 = hi2 := Int.le_antisymm hab.right hba.right
      congr 1
  le_trans := by
    intro a b c hab hbc
    cases a <;> cases b <;> cases c
    all_goals (simp_all [LE.le, Interval.le])
    rename_i lo1 hi1 ha lo2 hi2 hb lo3 hi3 hc
    apply And.intro
    · exact Int.le_trans hbc.left hab.left
    · exact Int.le_trans hab.right hbc.right

instance : BoundedJoinSemilattice Interval where
  sup := Interval.sup
  bot := .empty
  bot_le := by
    intro a
    simp [Interval.le, LE.le]
  le_sup_left := by
    intro a b
    -- cases a <;> cases b <;> simp [Interval.sup]
    -- · apply PartialOrder.le_refl
    -- · trivial
    -- · apply And.intro <;> apply Int.le_refl
    -- · exact ⟨Int.min_le_left _ _, Int.le_max_left _ _⟩
    simp [Interval.sup]
    split
    · trivial
    · apply PartialOrder.le_refl
    · apply And.intro
      · apply Int.min_le_left
      · apply Int.le_max_left
  le_sup_right := by
    intro a b
    cases a <;> cases b <;> simp [Interval.sup, Interval.le, LE.le]
    · apply And.intro <;> apply Int.le_refl
    · apply And.intro
      · apply Int.min_le_right
      · apply Int.le_max_right
  sup_le := by
    intro a b c hac hbc
    cases a <;> cases b <;> cases c <;> simp [Interval.sup]
    any_goals contradiction
    any_goals trivial
    simp [Interval.le, LE.le] at hac hbc
    apply And.intro
    · apply Int.le_min.mpr
      exact ⟨hac.left, hbc.left⟩
    · apply Int.max_le.mpr
      exact ⟨hac.right, hbc.right⟩

deriving instance DecidableEq for Interval

def Interval.add (a b : Interval) : Interval :=
  match a, b with
  | .empty        , _               => .empty
  | _             , .empty          => .empty
  | .range l1 h1 _, .range l2 h2 _  => .range (l1 + l2) (h1 + h2) (by omega)

def Interval.sub : Interval → Interval → Interval
  | .empty        , _               => .empty
  | _             , .empty          => .empty
  | .range l1 h1 _, .range l2 h2 _  => .range (l1 - h2) (h1 - l2) (by omega)
