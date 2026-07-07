/- ============================================================
   From Zero to Propagators
   Orders, Lattices, and Propagator Networks in Lean 4

   Companion verification file for the book
   `order-lattices/from-zero-to-propagators.tex`.

   Every Lean listing printed in the book is reproduced here and
   type-checked against toolchain leanprover/lean4:v4.28.0 with no
   external libraries. Every runtime output claimed in the book is
   reproduced by the `#eval`s below.

   Layout (follows the book):
     §1  Chapter 1 — Relations and Partial Orders
     §2  Chapter 2 — Special Elements and Monotone Maps
     §3  Chapter 3 — Lattices
     §4  Chapter 4 — Complete Lattices and Knaster–Tarski
     §5  Chapter 5 — The Propagator Model
     §6  Chapter 6 — A Propagator Network (FlatNat)
     §7  Chapter 7 — The Interval Lattice
     §8  Chapter 8 — Capstone I: Sudoku
     §9  Chapter 9 — Capstone II: Type Inference
     §A  Appendix  — Quick-reference snippets
     §P  Appendix  — Tactic & construct primer examples
     §S  Selected Solutions
   ============================================================ -/

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/- ============================================================
   §1  Chapter 1 — Relations and Partial Orders
   ============================================================ -/

-- A binary relation on type α
def Rel (α : Type) : Type := α → α → Prop

namespace OrderBook

def Reflexive  {α : Type} (r : Rel α) : Prop :=
  ∀ (a : α), r a a

def Symmetric  {α : Type} (r : Rel α) : Prop :=
  ∀ (a b : α), r a b → r b a

def Antisymm   {α : Type} (r : Rel α) : Prop :=
  ∀ (a b : α), r a b → r b a → a = b

def Transitive {α : Type} (r : Rel α) : Prop :=
  ∀ (a b c : α), r a b → r b c → r a c

-- Our own partial order typeclass (mirrors core Lean / Mathlib).
class PartialOrder (α : Type) where
  le         : α → α → Prop
  le_refl    : ∀ (a : α), le a a
  le_antisymm: ∀ (a b : α), le a b → le b a → a = b
  le_trans   : ∀ (a b c : α), le a b → le b c → le a c

-- Attach the ≤ notation to any PartialOrder instance.
instance [PartialOrder α] : LE α := ⟨PartialOrder.le⟩

-- A convenience alias for strict less-than
def lt [PartialOrder α] (a b : α) : Prop :=
  PartialOrder.le a b ∧ ¬ (a = b)

instance [PartialOrder α] : LT α := ⟨lt⟩

end OrderBook

instance : OrderBook.PartialOrder Nat where
  le          := (· ≤ ·)      -- uses Nat.le which is in core
  le_refl     := Nat.le_refl
  le_antisymm := fun a b h1 h2 => Nat.le_antisymm h1 h2
  le_trans    := fun a b c h1 h2 => Nat.le_trans h1 h2

-- ── Divisibility on a newtype wrapper ───────────────────────

structure DvdNat where
  val : Nat

instance : Coe DvdNat Nat := ⟨DvdNat.val⟩

instance {n : Nat} : OfNat DvdNat n := ⟨⟨n⟩⟩

def Dvd' (n m : DvdNat) : Prop := ∃ k : Nat, m.val = n.val * k

instance : LE DvdNat := ⟨Dvd'⟩

-- Lemma 1: if 0 | m, then m.val = 0.
theorem dvd_zero_left (m : DvdNat) (h : Dvd' ⟨0⟩ m) : m.val = 0 := by
  obtain ⟨k, hk⟩ := h
  simp at hk
  exact hk

-- Lemma 2: in ℕ, k * j = 1 forces k = 1.
-- (The calc chain is stated in the ≤ direction: core Lean ships a
-- Trans instance for ≤ but not for ≥.)
theorem mul_eq_one_left {k j : Nat} (h : k * j = 1) : k = 1 := by
  match k with
  | 0 =>
    simp [Nat.zero_mul] at h
  | 1 =>
    rfl
  | k + 2 =>
    exfalso
    have hj : j ≥ 1 := by
      cases j with
      | zero   => simp [Nat.mul_zero] at h
      | succ j => exact Nat.succ_le_succ (Nat.zero_le j)
    have hbig : 2 ≤ (k + 2) * j :=
      calc 2 ≤ k + 2         := Nat.le_add_left 2 k
        _ = (k + 2) * 1      := (Nat.mul_one (k + 2)).symm
        _ ≤ (k + 2) * j      := Nat.mul_le_mul_left (k + 2) hj
    omega

theorem mul_eq_one_right {k j : Nat} (h : k * j = 1) : j = 1 :=
  mul_eq_one_left (by rw [Nat.mul_comm]; exact h)

-- Lemma 3: if a > 0, a | b and b | a, then a = b.
theorem dvd_antisymm_pos
    {a b : Nat} (ha : 0 < a)
    (k : Nat) (hk : b = a * k)
    (j : Nat) (hj : a = b * j) : a = b := by
  have hkj : k * j = 1 := by
    have hstep : a = a * (k * j) :=
      calc a = b * j       := hj
           _ = (a * k) * j := by rw [hk]
           _ = a * (k * j) := by rw [Nat.mul_assoc]
    exact Nat.eq_of_mul_eq_mul_left ha (by rw [Nat.mul_one]; exact hstep.symm)
  have hj1 : j = 1 := mul_eq_one_right hkj
  have h₂ : a = b * 1 := by rw [hj1] at hj; exact hj
  rw [Nat.mul_one] at h₂
  exact h₂

open OrderBook in
instance : PartialOrder DvdNat where

  -- The order itself: divisibility.
  le := Dvd'

  -- Reflexivity: n | n via witness k = 1, since n.val = n.val * 1.
  le_refl := fun n =>
    ⟨1, (Nat.mul_one n.val).symm⟩

  -- Antisymmetry: expose the divisibility witnesses, then case-split
  -- on whether n.val is zero or positive, delegating to Lemma 1 or
  -- Lemma 3 respectively.
  le_antisymm := fun n m hnm hmn => by
    obtain ⟨k, hk⟩ := hnm
    obtain ⟨j, hj⟩ := hmn
    -- Reduce  n = m  (DvdNat equality) to  a = b  on the .val fields:
    -- cases exposes the fields, congr 1 splits the constructor.
    cases n; cases m
    congr 1
    rename_i a b
    cases Nat.eq_zero_or_pos a with
    | inl ha =>
      -- a = 0: b = 0 * k = 0 by Lemma 1, and a = 0, so a = b.
      subst ha
      exact (dvd_zero_left ⟨b⟩ ⟨k, hk⟩).symm
    | inr ha =>
      -- a > 0: use Lemma 3 directly.
      exact dvd_antisymm_pos ha k hk j hj

  -- Transitivity: compose witnesses.  b.val = a.val * k and
  -- c.val = b.val * j, so c.val = a.val * (k * j).
  le_trans := fun a b c ⟨k, hk⟩ ⟨j, hj⟩ =>
    ⟨k * j, by rw [hj, hk, Nat.mul_assoc]⟩

-- ── Sets as predicates ───────────────────────────────────────

def Set (α : Type) : Type := α → Prop

def Set.subset {α : Type} (s t : Set α) : Prop :=
  ∀ (a : α), s a → t a

instance {α : Type} : OrderBook.PartialOrder (Set α) where
  le          := Set.subset
  le_refl     := fun s a ha => ha
  le_antisymm := fun s t h1 h2 =>
    funext (fun a => propext ⟨h1 a, h2 a⟩)
  le_trans    := fun s t u h1 h2 a ha => h2 a (h1 a ha)

-- ── Computation interlude: the divisibility order on D12 ─────

def D12 : List Nat := [1, 2, 3, 4, 6, 12]
def dvd12 (a b : Nat) : Bool := b % a == 0

def upperBounds (xs : List Nat) : List Nat :=
  D12.filter (fun u => xs.all (fun x => dvd12 x u))

def sup12 (xs : List Nat) : Option Nat :=
  let ubs := upperBounds xs
  ubs.find? (fun s => ubs.all (fun u => dvd12 s u))

#eval sup12 [4, 6]   -- some 12  (lcm)  ✓ verified
#eval sup12 [2, 3]   -- some 6          ✓ verified

def lowerBounds (xs : List Nat) : List Nat :=
  D12.filter (fun l => xs.all (fun x => dvd12 l x))

def inf12 (xs : List Nat) : Option Nat :=
  let lbs := lowerBounds xs
  lbs.find? (fun s => lbs.all (fun l => dvd12 l s))

#eval inf12 [4, 6]   -- some 2  (gcd)   ✓ verified
#eval inf12 [3, 4]   -- some 1          ✓ verified

def covers (a b : Nat) : Bool :=
  dvd12 a b && a != b &&
  !D12.any (fun c => c != a && c != b && dvd12 a c && dvd12 c b)

def printHasse : IO Unit := do
  for a in D12 do
    for b in D12 do
      if covers a b then IO.println s!"{a} ──► {b}"

#eval printHasse  -- 1→2, 1→3, 2→4, 2→6, 3→6, 4→12, 6→12  ✓ verified

-- ── Chapter 1 exercises with printed solutions ───────────────

-- Exercise 1.1
open OrderBook in
theorem symm_antisymm_eq {α : Type} (r : Rel α)
    (hs : Symmetric r) (ha : Antisymm r) :
    ∀ a b : α, r a b → a = b := by
  intro a b h
  exact ha a b h (hs a b h)

-- Exercise 1.3 (product order)
open OrderBook in
instance [OrderBook.PartialOrder α] [OrderBook.PartialOrder β] :
    OrderBook.PartialOrder (α × β) where
  le p q := PartialOrder.le p.1 q.1 ∧ PartialOrder.le p.2 q.2
  le_refl := fun ⟨a, b⟩ => ⟨PartialOrder.le_refl a,
                              PartialOrder.le_refl b⟩
  le_antisymm := fun ⟨a1,b1⟩ ⟨a2,b2⟩ ⟨h1,h2⟩ ⟨h3,h4⟩ => by
    have := PartialOrder.le_antisymm _ _ h1 h3
    have := PartialOrder.le_antisymm _ _ h2 h4
    simp_all
  le_trans := fun ⟨a1,b1⟩ ⟨a2,b2⟩ ⟨a3,b3⟩ ⟨h1,h2⟩ ⟨h3,h4⟩ =>
    ⟨PartialOrder.le_trans _ _ _ h1 h3,
     PartialOrder.le_trans _ _ _ h2 h4⟩

/- ============================================================
   §2  Chapter 2 — Special Elements and Monotone Maps
   ============================================================ -/

namespace OrderBook

-- Bottom and top elements
class Bot (α : Type) where bot : α
class Top (α : Type) where top : α

notation "⊥" => Bot.bot
notation "⊤" => Top.top

-- Being a bounded partial order
class BoundedPartialOrder (α : Type) extends PartialOrder α, Bot α, Top α where
  bot_le : ∀ (a : α), (⊥ : α) ≤ a
  le_top : ∀ (a : α), a ≤ (⊤ : α)

end OrderBook

structure IsSupOf {α : Type} [OrderBook.PartialOrder α]
    (a b sup : α) : Prop where
  ge_a  : a ≤ sup
  ge_b  : b ≤ sup
  least : ∀ (u : α), a ≤ u → b ≤ u → sup ≤ u

theorem sup_unique {α : Type} [OrderBook.PartialOrder α]
    {a b s t : α}
    (hs : IsSupOf a b s) (ht : IsSupOf a b t) : s = t := by
  apply OrderBook.PartialOrder.le_antisymm
  · exact hs.least t ht.ge_a ht.ge_b
  · exact ht.least s hs.ge_a hs.ge_b

namespace OrderBook

structure Monotone {α β : Type}
    [PartialOrder α] [PartialOrder β] (f : α → β) : Prop where
  map_le : ∀ (a b : α), a ≤ b → f a ≤ f b

-- Composition of monotone maps is monotone
theorem Monotone.comp {α β γ : Type}
    [PartialOrder α] [PartialOrder β] [PartialOrder γ]
    {f : α → β} {g : β → γ}
    (hf : Monotone f) (hg : Monotone g) : Monotone (g ∘ f) where
  map_le := fun a b h => hg.map_le _ _ (hf.map_le _ _ h)

end OrderBook

-- ── Chapter 2 computation interlude ─────────────────────────

def isMonotone (f : Nat → Nat) : Bool :=
  D12.all (fun a =>
  D12.all (fun b =>
    !dvd12 a b || dvd12 (f a) (f b)))

#eval isMonotone id                         -- true   ✓ verified
#eval isMonotone (· * 2)                   -- true   ✓ verified
#eval isMonotone (fun n => 12 / n)         -- false  ✓ verified
#eval isMonotone (fun n => 12 / (12 / n)) -- true   ✓ verified

def fixedPoints (f : Nat → Nat) : List Nat :=
  D12.filter (fun x => f x == x)

#eval fixedPoints id                    -- [1, 2, 3, 4, 6, 12]  ✓ verified
#eval fixedPoints (fun _ => 1)          -- [1]                  ✓ verified
#eval D12.filter (fun n => 12 / n == n) -- []                   ✓ verified

def iterToFixpoint (f : Nat → Nat) (start : Nat) (limit : Nat) : List Nat :=
  let rec go (x : Nat) (n : Nat) (acc : List Nat) : List Nat :=
    if n = 0 then acc.reverse
    else let y := f x
         if y == x then (acc.reverse ++ [x])
         else go y (n - 1) (x :: acc)
  go start limit []

def double12 (n : Nat) : Nat :=
  if D12.contains (n * 2) then n * 2 else n

#eval iterToFixpoint double12 1 10   -- [1, 2, 4]   ✓ verified (8 ∉ D12, so 4 is a fixed point)
#eval iterToFixpoint double12 3 10   -- [3, 6, 12]  ✓ verified
#eval iterToFixpoint double12 12 10  -- [12]        ✓ verified

/- ============================================================
   §3  Chapter 3 — Lattices
   ============================================================ -/

namespace OrderBook

class Lattice (α : Type) extends PartialOrder α where
  inf : α → α → α    -- meet  (⊓)
  sup : α → α → α    -- join  (⊔)
  inf_le_left  : ∀ (a b : α), inf a b ≤ a
  inf_le_right : ∀ (a b : α), inf a b ≤ b
  le_inf : ∀ (a b c : α), a ≤ b → a ≤ c → a ≤ inf b c
  sup_le_left  : ∀ (a b : α), a ≤ sup a b
  sup_le_right : ∀ (a b : α), b ≤ sup a b
  le_sup : ∀ (a b c : α), a ≤ c → b ≤ c → sup a b ≤ c

infixl:70 " ⊓ " => Lattice.inf
infixl:65 " ⊔ " => Lattice.sup

end OrderBook

namespace OrderBook
open Lattice PartialOrder

variable {α : Type} [Lattice α]

theorem inf_comm (a b : α) : a ⊓ b = b ⊓ a := by
  apply le_antisymm
  · apply le_inf
    · exact inf_le_right a b
    · exact inf_le_left a b
  · apply le_inf
    · exact inf_le_right b a
    · exact inf_le_left b a

theorem inf_idem (a : α) : a ⊓ a = a := by
  apply le_antisymm
  · exact inf_le_left a a
  · exact le_inf a a a (le_refl a) (le_refl a)

theorem sup_comm (a b : α) : a ⊔ b = b ⊔ a := by
  apply le_antisymm
  · apply le_sup
    · exact sup_le_right b a
    · exact sup_le_left b a
  · apply le_sup
    · exact sup_le_right a b
    · exact sup_le_left a b

theorem sup_inf_self (a b : α) : a ⊔ (a ⊓ b) = a := by
  apply le_antisymm
  · apply le_sup
    · exact le_refl a
    · exact inf_le_left a b
  · exact sup_le_left a (a ⊓ b)

end OrderBook

-- ── Duality ──────────────────────────────────────────────────

structure Dual (α : Type) where
  val : α

-- Step 1: flip ≤.  a ≤_dual b  means  b.val ≤_orig a.val.
instance {α : Type} [LE α] : LE (Dual α) where
  le a b := LE.le (α := α) b.val a.val

-- Step 2: the dual partial order. Our PartialOrder class carries its
-- own `le` field, so the flipped order is stated again here (the LE
-- instance above only supplies notation).
open OrderBook in
instance {α : Type} [PartialOrder α] : PartialOrder (Dual α) where
  le a b := PartialOrder.le (α := α) b.val a.val
  le_refl a := PartialOrder.le_refl (α := α) a.val
  le_antisymm a b h1 h2 := by
    cases a; cases b; congr 1
    exact PartialOrder.le_antisymm (α := α) _ _ h2 h1
  le_trans a b c h1 h2 := by
    cases a; cases b; cases c
    exact PartialOrder.le_trans (α := α) _ _ _ h2 h1

-- Step 3: the dual lattice swaps inf and sup.
open OrderBook in
instance {α : Type} [Lattice α] : Lattice (Dual α) where
  inf          := fun a b => ⟨Lattice.sup (α := α) a.val b.val⟩
  sup          := fun a b => ⟨Lattice.inf (α := α) a.val b.val⟩
  inf_le_left  := fun a b => Lattice.sup_le_left  (α := α) a.val b.val
  inf_le_right := fun a b => Lattice.sup_le_right (α := α) a.val b.val
  sup_le_left  := fun a b => Lattice.inf_le_left  (α := α) a.val b.val
  sup_le_right := fun a b => Lattice.inf_le_right (α := α) a.val b.val
  le_inf := fun a b c h1 h2 => by
    change Lattice.sup (α := α) b.val c.val ≤ a.val
    exact Lattice.le_sup (α := α) b.val c.val a.val h1 h2
  le_sup := fun a b c h1 h2 => by
    change LE.le (α := α) c.val (Lattice.inf (α := α) a.val b.val)
    exact Lattice.le_inf (α := α) c.val a.val b.val h1 h2

-- ── The two-element lattice Bool ─────────────────────────────

-- Core's Bool.le_antisymm / Bool.le_trans take their element
-- arguments implicitly, so we eta-expand them to match the class
-- fields, which declare the elements explicitly.
instance : OrderBook.Lattice Bool where
  le          := (· ≤ ·)
  le_refl     := Bool.le_refl
  le_antisymm := fun a b => Bool.le_antisymm
  le_trans    := fun a b c => Bool.le_trans
  inf         := (· && ·)
  sup         := (· || ·)
  inf_le_left  := by decide
  inf_le_right := by decide
  le_inf       := by decide
  sup_le_left  := by decide
  sup_le_right := by decide
  le_sup       := by decide

-- ── The powerset lattice ─────────────────────────────────────

def Set.inter {α : Type} (s t : Set α) : Set α := fun a => s a ∧ t a
def Set.union {α : Type} (s t : Set α) : Set α := fun a => s a ∨ t a

instance {α : Type} : OrderBook.Lattice (Set α) where
  le          := Set.subset
  le_refl     := fun s a ha => ha
  le_antisymm := fun s t h1 h2 => funext fun a => propext ⟨h1 a, h2 a⟩
  le_trans    := fun s t u h1 h2 a ha => h2 a (h1 a ha)
  inf         := Set.inter
  sup         := Set.union
  inf_le_left  := fun s t a ⟨hs, _⟩ => hs
  inf_le_right := fun s t a ⟨_, ht⟩ => ht
  le_inf       := fun s t u hst hsu a ha => ⟨hst a ha, hsu a ha⟩
  sup_le_left  := fun s t a hs => Or.inl hs
  sup_le_right := fun s t a ht => Or.inr ht
  le_sup       := fun s t u hsu htu a h =>
    h.elim (hsu a) (htu a)

-- ── The divisibility lattice on Nat ──────────────────────────

instance : OrderBook.Lattice Nat where
  le          := (· ∣ ·)   -- divisibility
  le_refl     := Nat.dvd_refl
  le_antisymm := fun a b => Nat.dvd_antisymm
  le_trans    := fun a b c => Nat.dvd_trans
  inf         := Nat.gcd
  sup         := Nat.lcm
  inf_le_left  := Nat.gcd_dvd_left
  inf_le_right := Nat.gcd_dvd_right
  le_inf       := fun a b c => Nat.dvd_gcd
  sup_le_left  := Nat.dvd_lcm_left
  sup_le_right := Nat.dvd_lcm_right
  le_sup       := fun a b c ha hb => Nat.lcm_dvd ha hb

-- Exercise 3.3 (chapter version)
open OrderBook in
theorem le_iff_sup_eq {α : Type} [OrderBook.Lattice α] (a b : α) :
    a ≤ b ↔ a ⊔ b = b := by
  constructor
  · intro h
    apply PartialOrder.le_antisymm
    · exact Lattice.le_sup a b b h (PartialOrder.le_refl b)
    · exact Lattice.sup_le_right a b
  · intro h
    have : b = a ⊔ b := h.symm
    rw [this]
    exact Lattice.sup_le_left a b

/- ============================================================
   §4  Chapter 4 — Complete Lattices and Knaster–Tarski
   ============================================================ -/

namespace OrderBook

abbrev Pred (α : Type) := α → Prop

class CompleteLattice (α : Type) extends Lattice α where
  sSup : Pred α → α    -- supremum of a set  (a "big ⊔")
  sInf : Pred α → α    -- infimum of a set   (a "big ⊓")
  le_sSup : ∀ (s : Pred α) (a : α), s a → a ≤ sSup s
  sSup_le : ∀ (s : Pred α) (u : α), (∀ a, s a → a ≤ u) → sSup s ≤ u
  sInf_le : ∀ (s : Pred α) (a : α), s a → sInf s ≤ a
  le_sInf : ∀ (s : Pred α) (l : α), (∀ a, s a → l ≤ a) → l ≤ sInf s

end OrderBook

-- Set α is a complete lattice
instance {α : Type} : OrderBook.CompleteLattice (Set α) where
  sSup := fun F a => ∃ s : Set α, F s ∧ s a    -- union of a family
  sInf := fun F a => ∀ s : Set α, F s → s a    -- intersection of a family
  le_sSup := fun F s hs a ha => ⟨s, hs, ha⟩
  sSup_le := fun F u hu a ⟨s, hs, ha⟩ => hu s hs a ha
  sInf_le := fun F s hs a ha => ha s hs
  le_sInf := fun F l hl a ha s hs => hl s hs a ha
  le          := Set.subset
  le_refl     := fun s a h => h
  le_antisymm := fun s t h1 h2 => funext fun a => propext ⟨h1 a, h2 a⟩
  le_trans    := fun s t u h1 h2 a ha => h2 a (h1 a ha)
  inf         := Set.inter; sup := Set.union
  inf_le_left  := fun s t a ⟨hs,_⟩ => hs
  inf_le_right := fun s t a ⟨_,ht⟩ => ht
  le_inf       := fun s t u hst hsu a ha => ⟨hst a ha, hsu a ha⟩
  sup_le_left  := fun s t a hs => Or.inl hs
  sup_le_right := fun s t a ht => Or.inr ht
  le_sup       := fun s t u hsu htu a h => h.elim (hsu a) (htu a)

namespace OrderBook
open CompleteLattice PartialOrder

-- Knaster–Tarski: least fixed point of a monotone function
-- on a complete lattice
theorem knaster_tarski {α : Type} [CompleteLattice α]
    (f : α → α) (hf : Monotone f) :
    ∃ (lfp : α), f lfp = lfp ∧
      ∀ (x : α), f x = x → lfp ≤ x := by
  -- Define P = {x | f(x) ≤ x} and m = ⊓ P
  let P : Pred α := fun x => f x ≤ x
  let m := sInf P
  -- Step 1: f(m) ≤ m
  have step1 : f m ≤ m := by
    apply le_sInf
    intro x hx
    exact le_trans _ _ _ (hf.map_le m x (sInf_le P x hx)) hx
  -- Step 2: m ≤ f(m)  (f(m) ∈ P since f(f(m)) ≤ f(m))
  have step2 : m ≤ f m := by
    apply sInf_le
    exact hf.map_le _ _ step1
  have fixed : f m = m := le_antisymm _ _ step1 step2
  refine ⟨m, fixed, ?_⟩
  intro x hx
  apply sInf_le
  show f x ≤ x
  rw [hx]
  exact le_refl x

end OrderBook

/- ============================================================
   §5  Chapter 5 — The Propagator Model
   ============================================================ -/

namespace Propagators

class BoundedJoinSemilattice (α : Type) extends OrderBook.PartialOrder α where
  sup : α → α → α
  bot : α
  le_sup_left  : ∀ (a b : α), a ≤ sup a b
  le_sup_right : ∀ (a b : α), b ≤ sup a b
  sup_le       : ∀ (a b c : α), a ≤ c → b ≤ c → sup a b ≤ c
  bot_le       : ∀ (a : α), bot ≤ a

-- Convenient notation
infixl:65 " ⊔ " => BoundedJoinSemilattice.sup
notation    "⊥"  => BoundedJoinSemilattice.bot

structure Propagator1 (α β : Type)
    [BoundedJoinSemilattice α]
    [BoundedJoinSemilattice β] where
  fn       : α → β
  monotone : ∀ (a b : α), a ≤ b → fn a ≤ fn b

structure Propagator2 (α β γ : Type)
    [BoundedJoinSemilattice α]
    [BoundedJoinSemilattice β]
    [BoundedJoinSemilattice γ] where
  fn       : α → β → γ
  monotone : ∀ (a1 a2 : α) (b1 b2 : β),
    a1 ≤ a2 → b1 ≤ b2 → fn a1 b1 ≤ fn a2 b2

end Propagators

/- ============================================================
   §6  Chapter 6 — A Propagator Network (FlatNat)
   ============================================================ -/

-- §6.1 interlude: imperative Lean in half a page.
def imperativeTour : IO Unit := do
  let r ← IO.mkRef 0            -- a mutable reference holding a Nat
  let mut best := 0             -- a local mutable variable
  for i in [0:5] do             -- i runs over 0, 1, 2, 3, 4
    r.modify (· + i)            -- add i to the reference's contents
    if i > best then best := i
  let total ← r.get             -- read the reference back
  IO.println s!"total = {total}, best = {best}"

#eval imperativeTour   -- total = 10, best = 4

namespace Propagators

structure Cell (α : Type) where
  ref      : IO.Ref α

variable {α : Type} [BoundedJoinSemilattice α] [DecidableEq α]

def Cell.new : IO (Cell α) := do
  let r ← IO.mkRef (BoundedJoinSemilattice.bot (α := α))
  return { ref := r }

def Cell.read (c : Cell α) : IO α := c.ref.get

def Cell.write (c : Cell α) (v : α) : IO Bool := do
  let old ← c.ref.get
  let merged := old ⊔ v
  if merged == old then
    return false          -- no new information
  else
    c.ref.set merged
    return true           -- cell updated, re-schedule dependents

end Propagators

namespace Propagators

abbrev PropStep := IO Bool

def runToFixpoint (steps : Array PropStep) : IO Unit := do
  let mut changed := true
  while changed do
    changed := false
    for step in steps do
      let c ← step
      if c then changed := true

structure Network where
  steps    : Array PropStep

def Network.run (n : Network) : IO Unit :=
  runToFixpoint n.steps

end Propagators

namespace Propagators

inductive FlatNat where
  | unknown      : FlatNat         -- ⊥: no information
  | known (n : Nat) : FlatNat      -- exactly n
  | conflict     : FlatNat         -- ⊤: contradiction

-- We give the order a NAME rather than an anonymous match inside the
-- instance: later proofs can then unfold it with `simp [FlatNat.le]`,
-- and the rfl-lemma `le_def` below lets simp see through `≤`.
def FlatNat.le (a b : FlatNat) : Prop :=
  match a, b with
    | .unknown, _      => True     -- unknown ≤ everything
    | _, .conflict     => True     -- everything ≤ conflict
    | .known m, .known n => m = n  -- known values only ≤ themselves
    | .conflict, .unknown => False
    | .conflict, .known _ => False
    | .known _, .unknown  => False

instance : OrderBook.PartialOrder FlatNat where
  le := FlatNat.le
  le_refl  := by intro a; cases a <;> simp [FlatNat.le]
  le_antisymm := by
    intro a b hab hba
    cases a <;> cases b <;> simp_all [FlatNat.le]
  le_trans := by
    intro a b c hab hbc
    cases a <;> cases b <;> cases c <;> simp_all [FlatNat.le]

theorem FlatNat.le_def (a b : FlatNat) : (a ≤ b) = FlatNat.le a b := rfl

instance : BoundedJoinSemilattice FlatNat where
  le          := FlatNat.le
  le_refl     := OrderBook.PartialOrder.le_refl
  le_antisymm := OrderBook.PartialOrder.le_antisymm
  le_trans    := OrderBook.PartialOrder.le_trans
  bot         := .unknown
  sup a b := match a, b with
    | .unknown, x      => x
    | x, .unknown      => x
    | .known m, .known n => if m = n then .known m else .conflict
    | _, _             => .conflict
  bot_le      := by intro a; cases a <;> simp [FlatNat.le_def, FlatNat.le]
  le_sup_left  := by
    intro a b
    cases a <;> cases b <;> simp_all [FlatNat.le_def, FlatNat.le]
    rename_i m n
    by_cases h : m = n <;> simp [FlatNat.le_def, FlatNat.le, h]
  le_sup_right := by
    intro a b
    cases a <;> cases b <;> simp_all [FlatNat.le_def, FlatNat.le]
    rename_i m n
    by_cases h : m = n <;> simp [FlatNat.le_def, FlatNat.le, h]
  -- The known/known case needs its own `if m = n` split at the end.
  sup_le       := by
    intro a b c hac hbc
    cases a <;> cases b <;> cases c <;> simp_all [FlatNat.le_def, FlatNat.le]
    rename_i m n
    by_cases h : m = n <;> simp [FlatNat.le, h]

deriving instance DecidableEq for FlatNat

end Propagators

namespace Propagators

-- §6.4: pure functions with monotonicity proofs

def FlatNat.addFn : FlatNat → FlatNat → FlatNat
  | .known a,  .known b  => .known (a + b)
  | .conflict, _         => .conflict
  | _,         .conflict => .conflict
  | _,         _         => .unknown

def FlatNat.subFn (s x : FlatNat) : FlatNat :=
  match s, x with
  | .known total, .known a =>
      if total ≥ a then .known (total - a) else .conflict
  | .conflict, _ | _, .conflict => .conflict
  | _,         _               => .unknown

-- Proof: addFn is monotone.
-- Strategy: case-split all 81 constructor combinations (3 × 3 × 3 × 3);
-- simp_all with the unfolded order closes every case.
def addPropagator : Propagator2 FlatNat FlatNat FlatNat where
  fn       := FlatNat.addFn
  monotone := by
    intro a1 a2 b1 b2 ha hb
    cases a1 <;> cases a2 <;> cases b1 <;> cases b2
      <;> simp_all [FlatNat.addFn, FlatNat.le_def, FlatNat.le]

-- Proof: subFn is monotone. After the case split, the remaining goals
-- are stuck on `if` scrutinees; `split <;> simp_all` finishes them.
def subPropagator : Propagator2 FlatNat FlatNat FlatNat where
  fn       := FlatNat.subFn
  monotone := by
    intro a1 a2 b1 b2 ha hb
    cases a1 <;> cases a2 <;> cases b1 <;> cases b2
      <;> simp_all [FlatNat.subFn, FlatNat.le_def, FlatNat.le]
      <;> split <;> simp_all

-- §6.5: the running example.
open FlatNat

-- Addition propagator: addFn wrapped in IO — read the inputs, apply
-- the pure monotone function, merge the result into the output cell.
-- When either input is unknown, addFn returns unknown = ⊥, and
-- merging ⊥ changes nothing (write returns false). When an input is
-- conflict, addFn returns conflict — so contradictions propagate.
def addProp (cx cy csum : Cell FlatNat) : PropStep := do
  let x ← cx.read
  let y ← cy.read
  csum.write (FlatNat.addFn x y)

-- Subtraction (used to deduce y = sum - x): subFn wrapped in IO.
def subProp (csum cx cy : Cell FlatNat) : PropStep := do
  let s ← csum.read
  let x ← cx.read
  cy.write (FlatNat.subFn s x)

def exampleNetwork : IO Unit := do
  let cx   ← Cell.new (α := FlatNat)
  let cy   ← Cell.new (α := FlatNat)
  let csum ← Cell.new (α := FlatNat)

  -- Seed known facts
  let _ ← cx.write (.known 3)
  let _ ← csum.write (.known 10)

  let net : Network := {
    steps := #[
      addProp cx cy csum,
      subProp csum cx cy,
      subProp csum cy cx
    ]
  }

  net.run

  let yVal ← cy.read
  match yVal with
  | .known n => IO.println s!"y = {n}"   -- prints: y = 7  ✓ verified
  | .unknown  => IO.println "y is unknown"
  | .conflict => IO.println "contradiction!"

#eval exampleNetwork  -- y = 7  ✓ verified

end Propagators

/- ============================================================
   §7  Chapter 7 — The Interval Lattice
   ============================================================ -/

namespace Intervals

-- ── Bounds: Option Int with `none` as "unbounded" ────────────

-- A bound on an integer. `none` encodes "no bound at all":
-- read it as -∞ when it is a lower bound and +∞ when it is an
-- upper bound.
abbrev Bound := Option Int

-- Order on LOWER bounds: none = -∞ is the loosest lower bound.
def loLe : Bound → Bound → Prop
  | none,   _      => True
  | some _, none   => False
  | some a, some b => a ≤ b

-- Order on UPPER bounds: none = +∞ is the loosest upper bound.
def hiLe : Bound → Bound → Prop
  | _,      none   => True
  | none,   some _ => False
  | some a, some b => a ≤ b

-- A lower bound and an upper bound are consistent unless both are
-- finite and crossed (lo > hi).
def ordered : Bound → Bound → Prop
  | some l, some h => l ≤ h
  | _,      _      => True

instance : (l h : Bound) → Decidable (ordered l h)
  | none,   none   => isTrue True.intro
  | none,   some _ => isTrue True.intro
  | some _, none   => isTrue True.intro
  | some l, some h => inferInstanceAs (Decidable (l ≤ h))

-- The tighter of two lower bounds (their max, with none = -∞) …
def loMax : Bound → Bound → Bound
  | none, b => b
  | a, none => a
  | some a, some b => some (max a b)

-- … and the tighter of two upper bounds (their min, with none = +∞).
def hiMin : Bound → Bound → Bound
  | none, b => b
  | a, none => a
  | some a, some b => some (min a b)

-- Small lemmas about bounds. Each is a mechanical case split.
theorem loLe_refl (a : Bound) : loLe a a := by
  cases a <;> simp [loLe]

theorem hiLe_refl (a : Bound) : hiLe a a := by
  cases a <;> simp [hiLe]

theorem loLe_trans {a b c : Bound} : loLe a b → loLe b c → loLe a c := by
  cases a <;> cases b <;> cases c <;> simp [loLe] <;> omega

theorem hiLe_trans {a b c : Bound} : hiLe a b → hiLe b c → hiLe a c := by
  cases a <;> cases b <;> cases c <;> simp [hiLe] <;> omega

theorem loLe_antisymm {a b : Bound} : loLe a b → loLe b a → a = b := by
  cases a <;> cases b <;> simp [loLe] <;> omega

theorem hiLe_antisymm {a b : Bound} : hiLe a b → hiLe b a → a = b := by
  cases a <;> cases b <;> simp [hiLe] <;> omega

theorem loLe_max_left (a b : Bound) : loLe a (loMax a b) := by
  cases a <;> cases b <;> simp [loLe, loMax] <;> omega

theorem loLe_max_right (a b : Bound) : loLe b (loMax a b) := by
  cases a <;> cases b <;> simp [loLe, loMax] <;> omega

theorem loMax_le {a b c : Bound} : loLe a c → loLe b c → loLe (loMax a b) c := by
  cases a <;> cases b <;> cases c <;> simp [loLe, loMax] <;> omega

theorem hiMin_le_left (a b : Bound) : hiLe (hiMin a b) a := by
  cases a <;> cases b <;> simp [hiLe, hiMin] <;> omega

theorem hiMin_le_right (a b : Bound) : hiLe (hiMin a b) b := by
  cases a <;> cases b <;> simp [hiLe, hiMin] <;> omega

theorem le_hiMin {a b c : Bound} : hiLe c a → hiLe c b → hiLe c (hiMin a b) := by
  cases a <;> cases b <;> cases c <;> simp [hiLe, hiMin] <;> omega

-- If [l', h'] is a genuine interval squeezed between l and h,
-- then l and h cannot be crossed either.
theorem ordered_squeeze {l l' h' h : Bound} :
    loLe l l' → ordered l' h' → hiLe h' h → ordered l h := by
  cases l <;> cases l' <;> cases h' <;> cases h <;>
    simp [loLe, hiLe, ordered] <;> omega

-- ── The interval lattice ─────────────────────────────────────

inductive Interval where
  -- All integers between lo and hi (inclusive; none = unbounded).
  -- The proof field rules out crossed bounds like [8, 2].
  | range (lo hi : Bound) (ok : ordered lo hi) : Interval
  -- ⊤: no value is possible — a contradiction.
  | empty : Interval

-- ⊥: the interval (-∞, +∞) — "the value could be any integer".
def Interval.unbounded : Interval := .range none none True.intro

-- The interval [l, h] with finite ends.
def Interval.between (l h : Int) (ok : l ≤ h := by omega) : Interval :=
  .range (some l) (some h) ok

-- Information order: narrower = more informative = HIGHER.
-- b sits above a exactly when b's bounds are at least as tight.
def Interval.le (a b : Interval) : Prop :=
  match a, b with
  | _, .empty                      => True    -- ⊤ is above everything
  | .empty, _                      => False
  | .range l1 h1 _, .range l2 h2 _ => loLe l1 l2 ∧ hiLe h2 h1

-- Join = INTERSECTION: merge two constraints by keeping the tighter
-- bound on each side. If the bounds cross, the constraints are
-- contradictory and the join is ⊤ = empty.
def Interval.sup (a b : Interval) : Interval :=
  match a, b with
  | .empty, _ | _, .empty => .empty
  | .range l1 h1 _, .range l2 h2 _ =>
    if ok : ordered (loMax l1 l2) (hiMin h1 h2)
    then .range (loMax l1 l2) (hiMin h1 h2) ok
    else .empty

theorem Interval.le_refl_thm : ∀ (a : Interval), Interval.le a a := by
  intro a
  cases a with
  | empty => exact True.intro
  | range l h ok => exact ⟨loLe_refl l, hiLe_refl h⟩

theorem Interval.le_antisymm_thm :
    ∀ (a b : Interval), Interval.le a b → Interval.le b a → a = b := by
  intro a b hab hba
  cases a with
  | empty =>
    cases b with
    | empty => rfl
    | range l h ok => exact absurd hab (fun h => h)
  | range l1 h1 ok1 =>
    cases b with
    | empty => exact absurd hba (fun h => h)
    | range l2 h2 ok2 =>
      have hab' : loLe l1 l2 ∧ hiLe h2 h1 := hab
      have hba' : loLe l2 l1 ∧ hiLe h1 h2 := hba
      have hl : l1 = l2 := loLe_antisymm hab'.1 hba'.1
      have hh : h1 = h2 := hiLe_antisymm hba'.2 hab'.2
      subst hl; subst hh
      rfl   -- the `ok` proofs agree by proof irrelevance

theorem Interval.le_trans_thm :
    ∀ (a b c : Interval), Interval.le a b → Interval.le b c → Interval.le a c := by
  intro a b c hab hbc
  cases c with
  | empty => cases a <;> exact True.intro
  | range l3 h3 ok3 =>
    cases b with
    | empty => exact absurd hbc (fun h => h)
    | range l2 h2 ok2 =>
      cases a with
      | empty => exact absurd hab (fun h => h)
      | range l1 h1 ok1 =>
        have hab' : loLe l1 l2 ∧ hiLe h2 h1 := hab
        have hbc' : loLe l2 l3 ∧ hiLe h3 h2 := hbc
        exact ⟨loLe_trans hab'.1 hbc'.1, hiLe_trans hbc'.2 hab'.2⟩

instance : OrderBook.PartialOrder Interval where
  le          := Interval.le
  le_refl     := Interval.le_refl_thm
  le_antisymm := Interval.le_antisymm_thm
  le_trans    := Interval.le_trans_thm

theorem Interval.bot_le_thm : ∀ (a : Interval), Interval.le Interval.unbounded a := by
  intro a
  cases a with
  | empty => exact True.intro
  | range l h ok => exact ⟨True.intro, True.intro⟩

theorem Interval.le_sup_left_thm :
    ∀ (a b : Interval), Interval.le a (Interval.sup a b) := by
  intro a b
  cases a with
  | empty => cases b <;> exact True.intro
  | range l1 h1 ok1 =>
    cases b with
    | empty => exact True.intro
    | range l2 h2 ok2 =>
      simp only [Interval.sup]
      split
      · exact ⟨loLe_max_left l1 l2, hiMin_le_left h1 h2⟩
      · exact True.intro

theorem Interval.le_sup_right_thm :
    ∀ (a b : Interval), Interval.le b (Interval.sup a b) := by
  intro a b
  cases a with
  | empty => cases b <;> exact True.intro
  | range l1 h1 ok1 =>
    cases b with
    | empty => exact True.intro
    | range l2 h2 ok2 =>
      simp only [Interval.sup]
      split
      · exact ⟨loLe_max_right l1 l2, hiMin_le_right h1 h2⟩
      · exact True.intro

theorem Interval.sup_le_thm :
    ∀ (a b c : Interval),
      Interval.le a c → Interval.le b c → Interval.le (Interval.sup a b) c := by
  intro a b c hac hbc
  cases a with
  | empty => cases c <;> exact hac
  | range l1 h1 ok1 =>
    cases b with
    | empty => cases c <;> exact hbc
    | range l2 h2 ok2 =>
      cases c with
      | empty =>
        simp only [Interval.sup]
        split <;> exact True.intro
      | range l3 h3 ok3 =>
        have hac' : loLe l1 l3 ∧ hiLe h3 h1 := hac
        have hbc' : loLe l2 l3 ∧ hiLe h3 h2 := hbc
        have hlo : loLe (loMax l1 l2) l3 := loMax_le hac'.1 hbc'.1
        have hhi : hiLe h3 (hiMin h1 h2) := le_hiMin hac'.2 hbc'.2
        simp only [Interval.sup]
        split
        · exact ⟨hlo, hhi⟩
        · -- the "crossed bounds" branch is impossible: c is a genuine
          -- interval squeezed between the merged bounds.
          rename_i hbad
          exact absurd (ordered_squeeze hlo ok3 hhi) hbad

instance : Propagators.BoundedJoinSemilattice Interval where
  le          := Interval.le
  le_refl     := Interval.le_refl_thm
  le_antisymm := Interval.le_antisymm_thm
  le_trans    := Interval.le_trans_thm
  bot         := Interval.unbounded
  sup         := Interval.sup
  bot_le      := Interval.bot_le_thm
  le_sup_left  := Interval.le_sup_left_thm
  le_sup_right := Interval.le_sup_right_thm
  sup_le       := Interval.sup_le_thm

-- DecidableEq, needed by Cell.write. Two `range`s are equal iff their
-- bounds are; the `ok` proofs never disagree (proof irrelevance).
instance : DecidableEq Interval := fun a b =>
  match a, b with
  | .empty, .empty => isTrue rfl
  | .empty, .range _ _ _ => isFalse (fun h => Interval.noConfusion h)
  | .range _ _ _, .empty => isFalse (fun h => Interval.noConfusion h)
  | .range l1 h1 _, .range l2 h2 _ =>
    if h : l1 = l2 ∧ h1 = h2 then
      isTrue (by obtain ⟨rfl, rfl⟩ := h; rfl)
    else
      isFalse (fun heq => by cases heq; exact h ⟨rfl, rfl⟩)

-- ── Interval arithmetic ──────────────────────────────────────

-- Adding bounds: if either end is unbounded, so is the sum.
def addBound : Bound → Bound → Bound
  | some a, some b => some (a + b)
  | _,      _      => none

def subBound : Bound → Bound → Bound
  | some a, some b => some (a - b)
  | _,      _      => none

theorem ordered_addBound {l1 h1 l2 h2 : Bound} :
    ordered l1 h1 → ordered l2 h2 →
    ordered (addBound l1 l2) (addBound h1 h2) := by
  cases l1 <;> cases l2 <;> cases h1 <;> cases h2 <;>
    simp [ordered, addBound] <;> omega

theorem ordered_subBound {l1 h1 l2 h2 : Bound} :
    ordered l1 h1 → ordered l2 h2 →
    ordered (subBound l1 h2) (subBound h1 l2) := by
  cases l1 <;> cases l2 <;> cases h1 <;> cases h2 <;>
    simp [ordered, subBound] <;> omega

-- [l1,h1] + [l2,h2] = [l1+l2, h1+h2]
def Interval.add : Interval → Interval → Interval
  | .empty, _ | _, .empty => .empty
  | .range l1 h1 ok1, .range l2 h2 ok2 =>
    .range (addBound l1 l2) (addBound h1 h2) (ordered_addBound ok1 ok2)

-- [l1,h1] - [l2,h2] = [l1-h2, h1-l2]
def Interval.sub : Interval → Interval → Interval
  | .empty, _ | _, .empty => .empty
  | .range l1 h1 ok1, .range l2 h2 ok2 =>
    .range (subBound l1 h2) (subBound h1 l2) (ordered_subBound ok1 ok2)

-- ── Bound-propagation network ────────────────────────────────

def addConstraint
    (cx cy csum : Propagators.Cell Interval) : Array Propagators.PropStep :=
  #[
    -- Forward: sum ← x + y
    do
      let x ← cx.read; let y ← cy.read
      csum.write (Interval.add x y),
    -- Backward: x ← sum - y
    do
      let s ← csum.read; let y ← cy.read
      cx.write (Interval.sub s y),
    -- Backward: y ← sum - x
    do
      let s ← csum.read; let x ← cx.read
      cy.write (Interval.sub s x)
  ]

def showLo : Bound → String
  | none   => "-∞"
  | some n => toString n

def showHi : Bound → String
  | none   => "+∞"
  | some n => toString n

def Interval.show : Interval → String
  | .empty => "∅ (contradiction)"
  | .range l h _ => s!"[{showLo l}, {showHi h}]"

def intervalExample : IO Unit := do
  let cx   ← Propagators.Cell.new (α := Interval)
  let cy   ← Propagators.Cell.new (α := Interval)
  let csum ← Propagators.Cell.new (α := Interval)

  -- x ∈ [2, 8] and x + y = 10 (i.e. sum ∈ [10, 10])
  let _ ← cx.write (Interval.between 2 8)
  let _ ← csum.write (Interval.between 10 10)

  Propagators.runToFixpoint (addConstraint cx cy csum)

  IO.println s!"x   ∈ {Interval.show (← cx.read)}"
  IO.println s!"y   ∈ {Interval.show (← cy.read)}"
  IO.println s!"sum ∈ {Interval.show (← csum.read)}"

#eval intervalExample
-- x   ∈ [2, 8]
-- y   ∈ [2, 8]
-- sum ∈ [10, 10]
-- ✓ verified: the network quiesces (runToFixpoint returns) with both
-- the forward and the backward propagators installed.

end Intervals

/- ============================================================
   §8  Chapter 8 — Capstone I: Sudoku
   ============================================================ -/

namespace Sudoku

abbrev Digit := Fin 9

structure CandidateSet where
  present : Fin 9 → Bool

def CandidateSet.full : CandidateSet :=
  { present := fun _ => true }

def CandidateSet.empty : CandidateSet :=
  { present := fun _ => false }

def CandidateSet.singleton (d : Digit) : CandidateSet :=
  { present := fun i => i == d }

def CandidateSet.remove (s : CandidateSet) (d : Digit) : CandidateSet :=
  { present := fun i => s.present i && !(i == d) }

def CandidateSet.inter (s t : CandidateSet) : CandidateSet :=
  { present := fun i => s.present i && t.present i }

def CandidateSet.union (s t : CandidateSet) : CandidateSet :=
  { present := fun i => s.present i || t.present i }

-- The information order: s ≤ t iff t ⊆ s (t is more specific)
def CandidateSet.le (s t : CandidateSet) : Prop :=
  ∀ i : Digit, t.present i = true → s.present i = true

-- Antisymmetry: compare the two indicator functions pointwise
-- (rename_i names the functions exposed by `cases`).
instance : OrderBook.PartialOrder CandidateSet where
  le          := CandidateSet.le
  le_refl     := fun s i h => h
  le_antisymm := fun s t h1 h2 =>
    show s = t from by
      cases s; cases t
      congr 1; funext i
      rename_i sp tp
      cases hi : tp i
      · cases hs : sp i
        · rfl
        · exact absurd (h2 i hs) (by simp [hi])
      · exact h1 i hi
  le_trans    := fun s t u hst htu i hi => hst i (htu i hi)

-- `Bool.and_eq_true : ((a && b) = true) = (a = true ∧ b = true)` is
-- an equality of propositions, so we rewrite with `▸`.
instance : Propagators.BoundedJoinSemilattice CandidateSet where
  le          := CandidateSet.le
  le_refl     := fun s i h => h
  le_antisymm := OrderBook.PartialOrder.le_antisymm (α := CandidateSet)
  le_trans    := OrderBook.PartialOrder.le_trans (α := CandidateSet)
  bot         := CandidateSet.full
  sup         := CandidateSet.inter    -- ⊔ = ∩ in information order!
  bot_le      := fun s i _ => rfl
  le_sup_left  := fun s t i h => (Bool.and_eq_true _ _ ▸ h).1
  le_sup_right := fun s t i h => (Bool.and_eq_true _ _ ▸ h).2
  sup_le       := fun s t u hsu htu i h =>
    Bool.and_eq_true _ _ ▸ (⟨hsu i h, htu i h⟩ : _ ∧ _)

instance : DecidableEq CandidateSet :=
  fun s t =>
    if h : ∀ i, s.present i = t.present i
    then isTrue  (by cases s; cases t; congr 1; funext i; exact h i)
    else isFalse (fun heq => h (fun i => by rw [heq]))

-- ── The grid ─────────────────────────────────────────────────

abbrev Grid := Fin 9 → Fin 9 → Propagators.Cell CandidateSet

-- The `[·]!` index operators need an `Inhabited` fallback value;
-- `IO.Ref` provides none, so we allocate one dummy cell and bring a
-- local `Inhabited` instance into scope.
def makeGrid : IO Grid := do
  let mut rows : Array (Array (Propagators.Cell CandidateSet)) := #[]
  for _ in [:9] do
    let mut row : Array (Propagators.Cell CandidateSet) := #[]
    for _ in [:9] do
      let c ← Propagators.Cell.new (α := CandidateSet)
      row := row.push c
    rows := rows.push row
  let dummy ← Propagators.Cell.new (α := CandidateSet)
  have : Inhabited (Propagators.Cell CandidateSet) := ⟨dummy⟩
  return fun r c => rows[r.val]![c.val]!

def seedCell (grid : Grid) (r c : Fin 9) (d : Digit) : IO Unit := do
  let _ ← (grid r c).write (CandidateSet.singleton d)

-- ── Constraint propagators ───────────────────────────────────
-- Note the loop syntax: `for h : i in [:9]` binds, alongside i, a
-- proof `h` that i lies in the range; `h.upper : i < 9` is exactly
-- what the `Fin 9` constructor ⟨i, _⟩ needs.

def rowPropagator (grid : Grid) (r c : Fin 9) : Propagators.PropStep := do
  let cands ← (grid r c).read
  -- Check if this cell is a singleton
  let det : Option Digit := Id.run do
    let mut found : Option Digit := none
    let mut count := 0
    for h : i in [:9] do
      let i' : Digit := ⟨i, h.upper⟩
      if cands.present i' then
        found := some i'; count := count + 1
    if count = 1 then found else none
  match det with
  | none   => return false
  | some d =>
    let mut changed := false
    for h : j in [:9] do
      let j' : Fin 9 := ⟨j, h.upper⟩
      if j' ≠ c then
        -- We re-read and merge
        let old ← (grid r j').read
        let upd := CandidateSet.inter old { present := fun i => !(i == d) }
        let c ← (grid r j').write upd
        if c then changed := true
    return changed

def colPropagator (grid : Grid) (r c : Fin 9) : Propagators.PropStep := do
  let cands ← (grid r c).read
  let det : Option Digit := Id.run do
    let mut found : Option Digit := none
    let mut count := 0
    for h : i in [:9] do
      let i' : Digit := ⟨i, h.upper⟩
      if cands.present i' then found := some i'; count := count + 1
    if count = 1 then found else none
  match det with
  | none => return false
  | some d =>
    let mut changed := false
    for h : i in [:9] do
      let i' : Fin 9 := ⟨i, h.upper⟩
      if i' ≠ r then
        let old ← (grid i' c).read
        let upd := CandidateSet.inter old { present := fun k => !(k == d) }
        let ch ← (grid i' c).write upd
        if ch then changed := true
    return changed

def boxPropagator (grid : Grid) (r c : Fin 9) : Propagators.PropStep := do
  let cands ← (grid r c).read
  let det : Option Digit := Id.run do
    let mut found : Option Digit := none; let mut count := 0
    for h : i in [:9] do
      let i' : Digit := ⟨i, h.upper⟩
      if cands.present i' then found := some i'; count := count + 1
    if count = 1 then found else none
  match det with
  | none => return false
  | some d =>
    let boxR := r.val / 3 * 3
    let boxC := c.val / 3 * 3
    let mut changed := false
    for hr : dr in [:3] do
      for hc : dc in [:3] do
        let r' : Fin 9 := ⟨boxR + dr, by have h1 : dr < 3 := hr.upper; have := r.isLt; omega⟩
        let c' : Fin 9 := ⟨boxC + dc, by have h2 : dc < 3 := hc.upper; have := c.isLt; omega⟩
        if !(r' = r && c' = c) then
          let old ← (grid r' c').read
          let upd := CandidateSet.inter old { present := fun k => !(k == d) }
          let ch ← (grid r' c').write upd
          if ch then changed := true
    return changed

-- ── Assembling and running the solver ────────────────────────

def buildNetwork (grid : Grid) : Array Propagators.PropStep := Id.run do
  let mut steps : Array Propagators.PropStep := #[]
  for hr : r in [:9] do
    for hc : c in [:9] do
      let r' : Fin 9 := ⟨r, hr.upper⟩
      let c' : Fin 9 := ⟨c, hc.upper⟩
      steps := steps.push (rowPropagator grid r' c')
      steps := steps.push (colPropagator grid r' c')
      steps := steps.push (boxPropagator grid r' c')
  return steps

def printGrid (grid : Grid) : IO Unit := do
  for hr : r in [:9] do
    let mut row := ""
    for hc : c in [:9] do
      let r' : Fin 9 := ⟨r, hr.upper⟩
      let c' : Fin 9 := ⟨c, hc.upper⟩
      let cands ← (grid r' c').read
      let mut digit := '?'
      let mut count := 0
      for h : i in [:9] do
        let i' : Digit := ⟨i, h.upper⟩
        if cands.present i' then digit := Char.ofNat (i + 49); count := count + 1
      row := row ++ (if count = 1 then s!"{digit}" else "?")
      if c % 3 == 2 && c < 8 then row := row ++ "|"
    IO.println row
    if r % 3 == 2 && r < 8 then IO.println "-----------"

def examplePuzzle : Array (Array Nat) := #[
  #[5, 3, 0, 0, 7, 0, 0, 0, 0],
  #[6, 0, 0, 1, 9, 5, 0, 0, 0],
  #[0, 9, 8, 0, 0, 0, 0, 6, 0],
  #[8, 0, 0, 0, 6, 0, 0, 0, 3],
  #[4, 0, 0, 8, 0, 3, 0, 0, 1],
  #[7, 0, 0, 0, 2, 0, 0, 0, 6],
  #[0, 6, 0, 0, 0, 0, 2, 8, 0],
  #[0, 0, 0, 4, 1, 9, 0, 0, 5],
  #[0, 0, 0, 0, 8, 0, 0, 7, 9]
]

-- The dependent `if h : 1 ≤ d ∧ d ≤ 9` hands omega the bound it
-- needs to build the `Fin 9` seed value `⟨d - 1, _⟩`.
def solveSudoku : IO Unit := do
  let grid ← makeGrid
  for hr : r in [:9] do
    for hc : c in [:9] do
      let d := examplePuzzle[r]![c]!
      if h : 1 ≤ d ∧ d ≤ 9 then
        let r' : Fin 9 := ⟨r, hr.upper⟩
        let c' : Fin 9 := ⟨c, hc.upper⟩
        seedCell grid r' c' ⟨d - 1, by omega⟩
  let steps := buildNetwork grid
  Propagators.runToFixpoint steps
  IO.println "Solution:"
  printGrid grid

-- ✓ verified: propagation alone fully solves this puzzle; the output
-- matches the known unique solution of the classic example puzzle:
--   534|678|912
--   672|195|348
--   198|342|567
--   -----------
--   859|761|423
--   426|853|791
--   713|924|856
--   -----------
--   961|537|284
--   287|419|635
--   345|286|179
#eval solveSudoku

end Sudoku

/- ============================================================
   §9  Chapter 9 — Capstone II: Type Inference
   ============================================================ -/

namespace TypeInfer

inductive Expr where
  | intLit  (n : Int)        : Expr
  | boolLit (b : Bool)       : Expr
  | var     (x : String)     : Expr
  | add     (e1 e2 : Expr)   : Expr
  | ifExpr  (cond t f : Expr): Expr
  | lam     (x : String) (body : Expr) : Expr
  | app     (fn arg : Expr)  : Expr
  | letExpr (x : String) (e body : Expr) : Expr

inductive Ty where
  | unknown            : Ty    -- ⊥
  | int                : Ty
  | bool               : Ty
  | fun_ (dom cod : Ty): Ty    -- dom → cod
  | typeError          : Ty    -- ⊤

def Ty.unify : Ty → Ty → Ty
  | .unknown, t          => t
  | t, .unknown          => t
  | .typeError, _        => .typeError
  | _, .typeError        => .typeError
  | .int, .int           => .int
  | .bool, .bool         => .bool
  | .fun_ d1 c1, .fun_ d2 c2 => .fun_ (Ty.unify d1 d2) (Ty.unify c1 c2)
  | _, _                 => .typeError   -- incompatible types

def Ty.le : Ty → Ty → Prop
  | .unknown, _            => True
  | _, .typeError          => True
  | .int, .int             => True
  | .bool, .bool           => True
  | .fun_ d1 c1, .fun_ d2 c2 => Ty.le d1 d2 ∧ Ty.le c1 c2
  | _, _                   => False

-- The order laws are proved as standalone lemmas by structural
-- induction on the first argument (the recursive `fun_` constructor
-- needs genuine induction hypotheses), then plugged into the
-- instances as terms.

theorem Ty.le_refl_thm : ∀ (t : Ty), Ty.le t t := by
  intro t
  induction t <;> simp [Ty.le, *]

theorem Ty.le_antisymm_thm : ∀ (a b : Ty), Ty.le a b → Ty.le b a → a = b := by
  intro a
  induction a with
  | fun_ d c ihd ihc =>
    intro b h1 h2
    cases b <;> simp_all [Ty.le]
    exact ⟨ihd _ h1.1 h2.1, ihc _ h1.2 h2.2⟩
  | _ => intro b h1 h2; cases b <;> simp_all [Ty.le]

theorem Ty.le_trans_thm : ∀ (a b c : Ty), Ty.le a b → Ty.le b c → Ty.le a c := by
  intro a
  induction a with
  | fun_ d c ihd ihc =>
    intro b c' h1 h2
    cases b <;> cases c' <;> simp_all [Ty.le]
    exact ⟨ihd _ _ h1.1 h2.1, ihc _ _ h1.2 h2.2⟩
  | _ => intro b c' h1 h2; cases b <;> cases c' <;> simp_all [Ty.le]

theorem Ty.le_sup_left_thm : ∀ (a b : Ty), Ty.le a (Ty.unify a b) := by
  intro a
  induction a with
  | fun_ d c ihd ihc =>
    intro b
    cases b <;> simp [Ty.le, Ty.unify]
    · exact ⟨Ty.le_refl_thm d, Ty.le_refl_thm c⟩
    · exact ⟨ihd _, ihc _⟩
  | _ => intro b; cases b <;> simp [Ty.le, Ty.unify]

theorem Ty.le_sup_right_thm : ∀ (a b : Ty), Ty.le b (Ty.unify a b) := by
  intro a
  induction a with
  | fun_ d c ihd ihc =>
    intro b
    cases b <;> simp [Ty.le, Ty.unify]
    · exact ⟨ihd _, ihc _⟩
  | _ => intro b; cases b <;> simp [Ty.le, Ty.unify, Ty.le_refl_thm]

theorem Ty.sup_le_thm :
    ∀ (a b c : Ty), Ty.le a c → Ty.le b c → Ty.le (Ty.unify a b) c := by
  intro a
  induction a with
  | fun_ d c ihd ihc =>
    intro b c' h1 h2
    cases b <;> cases c' <;> simp_all [Ty.le, Ty.unify]
  | _ => intro b c' h1 h2; cases b <;> cases c' <;> simp_all [Ty.le, Ty.unify]

instance : OrderBook.PartialOrder Ty where
  le          := Ty.le
  le_refl     := Ty.le_refl_thm
  le_antisymm := Ty.le_antisymm_thm
  le_trans    := Ty.le_trans_thm

instance : Propagators.BoundedJoinSemilattice Ty where
  le          := Ty.le
  le_refl     := Ty.le_refl_thm
  le_antisymm := Ty.le_antisymm_thm
  le_trans    := Ty.le_trans_thm
  bot         := .unknown
  sup         := Ty.unify
  bot_le      := fun _ => trivial
  le_sup_left  := Ty.le_sup_left_thm
  le_sup_right := Ty.le_sup_right_thm
  sup_le       := Ty.sup_le_thm

deriving instance DecidableEq for Ty

-- ── Constraint generation ────────────────────────────────────

abbrev Context := List (String × Propagators.Cell Ty)

def Context.lookup (ctx : Context) (x : String) :
    Option (Propagators.Cell Ty) :=
  ctx.find? (fun p => p.1 == x) |>.map (·.2)

-- NB: `(·.push ...)` must be written without a space after the `·`.
partial def inferExpr
    (ctx : Context)
    (e : Expr)
    (steps : IO.Ref (Array Propagators.PropStep)) :
    IO (Propagators.Cell Ty) := do
  match e with
  | .intLit _ =>
    let c ← Propagators.Cell.new (α := Ty)
    let _ ← c.write .int
    return c

  | .boolLit _ =>
    let c ← Propagators.Cell.new (α := Ty)
    let _ ← c.write .bool
    return c

  | .var x =>
    match ctx.lookup x with
    | some c => return c
    | none   =>
      let c ← Propagators.Cell.new (α := Ty)
      let _ ← c.write .typeError  -- unbound variable
      return c

  | .add e1 e2 =>
    let c1 ← inferExpr ctx e1 steps
    let c2 ← inferExpr ctx e2 steps
    let cOut ← Propagators.Cell.new (α := Ty)
    -- Propagator: both operands must be Int. We then re-read the
    -- operand cells and merge their join into the output — so if an
    -- operand has jumped to typeError (e.g. Bool ⊔ Int), the error
    -- reaches the result cell too.
    steps.modify (·.push do
      let _ ← c1.write .int
      let _ ← c2.write .int
      let t1 ← c1.read; let t2 ← c2.read
      cOut.write (Ty.unify t1 t2))
    return cOut

  | .ifExpr cond t f =>
    let ccond ← inferExpr ctx cond steps
    let ct    ← inferExpr ctx t    steps
    let cf    ← inferExpr ctx f    steps
    let cOut  ← Propagators.Cell.new (α := Ty)
    steps.modify (·.push do
      let _ ← ccond.write .bool
      let tv ← ct.read; let fv ← cf.read
      let _ ← ct.write fv; let _ ← cf.write tv
      let tv' ← ct.read
      cOut.write tv')
    return cOut

  | .lam x body =>
    let cDom  ← Propagators.Cell.new (α := Ty)
    let ctx'  := (x, cDom) :: ctx
    let cBody ← inferExpr ctx' body steps
    let cOut  ← Propagators.Cell.new (α := Ty)
    steps.modify (·.push do
      let d ← cDom.read; let b ← cBody.read
      cOut.write (.fun_ d b))
    return cOut

  | .app fn arg =>
    let cFn  ← inferExpr ctx fn  steps
    let cArg ← inferExpr ctx arg steps
    let cOut ← Propagators.Cell.new (α := Ty)
    steps.modify (·.push do
      let fv ← cFn.read; let av ← cArg.read
      let ov ← cOut.read
      match fv with
      | .fun_ d r =>
        let _ ← cArg.write d   -- arg type must match domain
        let _ ← cOut.write r   -- result type from codomain
        let _ ← cFn.write (.fun_ av ov) -- refine fn type
        return false
      | .unknown =>
        let _ ← cFn.write (.fun_ av ov)
        return false
      | _ =>
        let _ ← cFn.write .typeError; return false)
    return cOut

  | .letExpr x e body =>
    let ce   ← inferExpr ctx  e    steps
    let ctx' := (x, ce) :: ctx
    inferExpr ctx' body steps

def infer (e : Expr) : IO Ty := do
  let stepsRef ← IO.mkRef (Array.empty : Array Propagators.PropStep)
  let cResult  ← inferExpr [] e stepsRef
  let steps    ← stepsRef.get
  Propagators.runToFixpoint steps
  cResult.read

def Ty.toString : Ty → String
  | .unknown       => "?"
  | .int           => "Int"
  | .bool          => "Bool"
  | .fun_ d r      => s!"({Ty.toString d} → {Ty.toString r})"
  | .typeError     => "TypeError"

def ex1 : Expr := .add (.intLit 1) (.intLit 2)
def ex2 : Expr := .lam "x" (.add (.var "x") (.intLit 1))
def ex3 : Expr := .ifExpr (.boolLit true) (.intLit 1) (.intLit 2)
def ex4 : Expr := .add (.boolLit true) (.intLit 1)

def runExamples : IO Unit := do
  for (name, e) in [("1 + 2", ex1), ("λx. x+1", ex2),
                    ("if true 1 2", ex3), ("true + 1", ex4)] do
    let ty ← infer e
    IO.println s!"{name} : {Ty.toString ty}"

-- ✓ verified:
--   1 + 2 : Int
--   λx. x+1 : (Int → Int)
--   if true 1 2 : Int
--   true + 1 : TypeError
#eval runExamples

end TypeInfer

/- ============================================================
   §A  Appendix — Quick-reference snippets
   ============================================================ -/

namespace AppendixA

#check Nat       -- Nat : Type          ✓ verified
#check Type      -- Type : Type 1       ✓ verified
#check Prop      -- Prop : Type         ✓ verified

def f : Nat → Nat → Nat := fun a b => a + b
def g (a b : Nat) : Nat := a + b    -- same, different syntax

-- (The book's `def myList (α : Type) (n : Nat) : Type := ...` is an
-- ellipsis placeholder; a concrete body is supplied here.)
def myList (α : Type) (n : Nat) : Type := Fin n → α

def h : Nat :=
  let x := 5
  let y := x + 1
  x * y

class MyClass (α : Type) where
  someMethod : α → Nat
  someProperty : ∀ (a : α), someMethod a ≥ 0

instance : MyClass Nat where
  someMethod := id
  someProperty := Nat.zero_le

def useMyClass [MyClass α] (a : α) : Nat :=
  MyClass.someMethod a

end AppendixA

/- ============================================================
   §P  Appendix — Tactic & construct primer examples
   (Every example printed in the Appendix primer, compile-checked.)
   ============================================================ -/

namespace Primer

-- ── intro / exact ────────────────────────────────────────────

theorem imp_demo (p q : Prop) (hq : q) : p → q ∧ q := by
  intro hp
  exact ⟨hq, hq⟩

-- ── apply ────────────────────────────────────────────────────

theorem apply_demo (a b : Nat) (h : a = b) : a ≤ b := by
  apply Nat.le_of_eq
  exact h

-- ── rfl ──────────────────────────────────────────────────────

example : 2 + 2 = 4 := rfl
example : (fun n : Nat => n + 1) 3 = 4 := rfl

-- ── constructor ──────────────────────────────────────────────

example : 1 ≤ 2 ∧ 2 ≤ 3 := by
  constructor
  · omega
  · omega

-- ── cases, and what it desugars to ───────────────────────────

theorem bool_or_not (b : Bool) : (b || !b) = true := by
  cases b with
  | false => rfl
  | true  => rfl

-- the same proof written directly against the recursor
theorem bool_or_not' (b : Bool) : (b || !b) = true :=
  Bool.rec (motive := fun x => (x || !x) = true) rfl rfl b

-- ── induction, and what it desugars to ───────────────────────

theorem zero_add_tac (n : Nat) : 0 + n = n := by
  induction n with
  | zero => rfl
  | succ k ih => rw [Nat.add_succ, ih]

-- the same proof as an explicit Nat.rec term
theorem zero_add_term (n : Nat) : 0 + n = n :=
  Nat.rec (motive := fun m => 0 + m = m)
    rfl
    (fun k ih => congrArg Nat.succ ih)
    n

-- ── obtain / rcases, and what they desugar to ────────────────

theorem pos_of_succ {n : Nat} (h : ∃ k, n = k + 1) : 0 < n := by
  obtain ⟨k, hk⟩ := h
  subst hk
  exact Nat.succ_pos k

-- as an application of the eliminator …
theorem pos_of_succ' {n : Nat} (h : ∃ k, n = k + 1) : 0 < n :=
  Exists.elim h (fun k hk => hk ▸ Nat.succ_pos k)

-- … or as a match
theorem pos_of_succ'' {n : Nat} (h : ∃ k, n = k + 1) : 0 < n :=
  match h with
  | ⟨k, hk⟩ => hk ▸ Nat.succ_pos k

-- ── rename_i ─────────────────────────────────────────────────

theorem rename_demo (o : Option Nat) (h : o ≠ none) : ∃ n, o = some n := by
  cases o
  · exact absurd rfl h
  · rename_i n     -- name the anonymous value introduced by `cases`
    exact ⟨n, rfl⟩

-- ── by_cases, and the Decidable `if` underneath ──────────────

theorem em_nat (n : Nat) : n = 0 ∨ n ≠ 0 := by
  by_cases h : n = 0
  · exact Or.inl h
  · exact Or.inr h

theorem em_nat' (n : Nat) : n = 0 ∨ n ≠ 0 :=
  if h : n = 0 then Or.inl h else Or.inr h

-- ── exfalso ──────────────────────────────────────────────────

theorem from_absurd_bounds (n : Nat) (h1 : n < 2) (h2 : 2 < n) :
    n = 42 := by
  exfalso
  omega

-- ── subst ────────────────────────────────────────────────────

theorem subst_demo (a b : Nat) (hab : a = b) (ha : a ≤ 5) : b ≤ 5 := by
  subst hab
  exact ha

-- ── calc, and the Trans instances underneath ─────────────────

theorem calc_demo (a b c d : Nat)
    (h1 : a ≤ b) (h2 : b ≤ c) (h3 : c ≤ d) : a ≤ d :=
  calc a ≤ b := h1
    _ ≤ c := h2
    _ ≤ d := h3

theorem calc_demo' (a b c d : Nat)
    (h1 : a ≤ b) (h2 : b ≤ c) (h3 : c ≤ d) : a ≤ d :=
  Trans.trans (Trans.trans h1 h2) h3

-- ── split ────────────────────────────────────────────────────

def absDiff (a b : Int) : Int := if a ≤ b then b - a else a - b

theorem absDiff_nonneg (a b : Int) : 0 ≤ absDiff a b := by
  simp only [absDiff]
  split <;> omega

-- ── change ───────────────────────────────────────────────────

example : (fun n : Nat => n + 2) 3 = 5 := by
  change 3 + 2 = 5
  rfl

-- ── simp / simp_all ──────────────────────────────────────────

theorem simp_demo (xs : List Nat) : (xs ++ []).length = xs.length := by
  simp

theorem simp_all_demo (xs : List Nat) (h : xs = [1, 2]) :
    xs.length = 2 := by
  simp_all

-- ── omega / decide ───────────────────────────────────────────

example (a b : Nat) (h : a + 2 * b = 10) (hb : 3 ≤ b) : a ≤ 4 := by
  omega

example : (15 % 4 = 3) ∧ (2 ^ 10 = 1024) := by decide
example : ∀ b : Bool, (b && !b) = false := by decide

-- ── have / show ──────────────────────────────────────────────

theorem have_demo (a : Nat) (h : a ≤ 3) : a ≤ 10 := by
  have h' : (3 : Nat) ≤ 10 := by omega
  show a ≤ 10
  exact Nat.le_trans h h'

-- ── funext / congr ───────────────────────────────────────────

theorem funext_demo : (fun n : Nat => n + 0) = (fun n : Nat => n) := by
  funext n
  rfl

structure Point where
  x : Int
  y : Int

theorem congr_demo (p q : Point) (hx : p.x = q.x) (hy : p.y = q.y) :
    p = q := by
  cases p; cases q
  congr 1   -- splits ⟨x₁,y₁⟩ = ⟨x₂,y₂⟩ into x₁ = x₂ and y₁ = y₂

-- ── do-notation, mut, for, while, Id.run ─────────────────────

def sumTo (n : Nat) : Nat := Id.run do
  let mut acc := 0
  for i in [0:n+1] do
    acc := acc + i
  return acc

#eval sumTo 10   -- 55

-- what the mut/for pair compiles down to (morally): a fold
def sumTo' (n : Nat) : Nat :=
  (List.range (n + 1)).foldl (fun acc i => acc + i) 0

#eval sumTo' 10  -- 55

def firstPowerAbove (bound : Nat) : IO Nat := do
  let mut p := 1
  while p ≤ bound do
    p := p * 2
  return p

#eval firstPowerAbove 100   -- 128

-- ── IO.Ref ───────────────────────────────────────────────────

def counterDemo : IO Nat := do
  let r ← IO.mkRef 0     -- allocate a mutable reference holding 0
  r.set 5                -- overwrite the contents
  r.modify (· + 1)       -- apply a function to the contents
  r.get                  -- read it back

#eval counterDemo        -- 6

-- ── partial def ──────────────────────────────────────────────

partial def collatzSteps (n : Nat) : Nat :=
  if n ≤ 1 then 0
  else if n % 2 == 0 then 1 + collatzSteps (n / 2)
  else 1 + collatzSteps (3 * n + 1)

#eval collatzSteps 6     -- 8

end Primer

/- ============================================================
   §S  Selected Solutions
   ============================================================ -/

-- Exercise 1.1 and 1.3 are identical to the chapter versions proved
-- in §1 above.

open OrderBook

-- Exercise 2.1 (antitone ∘ antitone = monotone)
-- NB: no `[LE _]` binders — OrderBook.PartialOrder already provides
-- the ≤ notation; a second LE instance would introduce an unrelated
-- order and the hypotheses would no longer match Monotone's.
theorem antitone_comp_antitone {α β γ : Type}
    [PartialOrder α] [PartialOrder β] [PartialOrder γ]
    {f : α → β} {g : β → γ}
    (hf : ∀ a b : α, a ≤ b → f b ≤ f a)
    (hg : ∀ a b : β, a ≤ b → g b ≤ g a) :
    Monotone (g ∘ f) where
  map_le := fun a b h => hg (f b) (f a) (hf a b h)

-- Exercise 2.2 (fixed points — ascending chain)
def iter {α : Type} (f : α → α) : Nat → α → α
  | 0,     x => x
  | n + 1, x => f (iter f n x)

theorem iter_chain {α : Type} [PartialOrder α]
    {f : α → α} (hf : Monotone f)
    {a : α} (ha : a ≤ f a) :
    ∀ n : Nat, iter f n a ≤ iter f (n + 1) a := by
  intro n
  induction n with
  | zero => exact ha
  | succ n ih => exact hf.map_le _ _ ih

-- Exercise 2.3 (identity is monotone)
theorem Monotone.id {α : Type} [PartialOrder α] :
    Monotone (id : α → α) where
  map_le := fun _ _ h => h

-- Exercise 3.1 (interval information order)
structure Interval where
  l      : Int
  h      : Int
  l_le_h : l ≤ h

instance : PartialOrder Interval where
  -- Information order: i ≤ j iff j is contained in i
  -- (narrower = more informative = higher).
  le := fun i j => i.l ≤ j.l ∧ j.h ≤ i.h
  le_refl := fun a => ⟨Int.le_refl a.l, Int.le_refl a.h⟩
  le_antisymm := fun a b hyp₁ hyp₂ => by
    cases a; cases b
    rename_i l₁ h₁ l₁_le_h₁ l₂ h₂ l₂_le_h₂
    congr 1
    · exact Int.le_antisymm hyp₁.left hyp₂.left
    · exact Int.le_antisymm hyp₂.right hyp₁.right
    -- the l_le_h field is closed by proof irrelevance
  le_trans := fun a b c hyp₁ hyp₂ => by
    rcases a with ⟨a_l, a_h, a_le⟩
    rcases b with ⟨b_l, b_h, b_le⟩
    rcases c with ⟨c_l, c_h, c_le⟩
    have hl_ab : a_l ≤ b_l := hyp₁.left
    have hl_bc : b_l ≤ c_l := hyp₂.left
    have hh_ba : b_h ≤ a_h := hyp₁.right
    have hh_cb : c_h ≤ b_h := hyp₂.right
    exact ⟨Int.le_trans hl_ab hl_bc, Int.le_trans hh_cb hh_ba⟩

-- Exercise 3.3 (solutions version; the chapter version is in §3)
theorem le_iff_sup_eq' {α : Type} [Lattice α] {a b : α} :
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

-- Exercise 3.4 (product lattice)
instance {α β : Type} [Lattice α] [Lattice β] : Lattice (α × β) where
  le            := fun a b => (a.fst ≤ b.fst) ∧ (a.snd ≤ b.snd)
  le_refl       := fun a => by
    apply And.intro
    · apply PartialOrder.le_refl
    · apply PartialOrder.le_refl
  le_antisymm {a b} := fun hyp₁ hyp₂ => by
    rcases a with ⟨l₁, r₁⟩; rcases b with ⟨l₂, r₂⟩; congr 1
    · exact PartialOrder.le_antisymm _ _ hyp₁.left hyp₂.left
    · exact PartialOrder.le_antisymm _ _ hyp₁.right hyp₂.right
  le_trans {a b c} := fun hyp₁ hyp₂ => by
    apply And.intro
    · exact PartialOrder.le_trans _ _ _ hyp₁.left hyp₂.left
    · exact PartialOrder.le_trans _ _ _ hyp₁.right hyp₂.right
  inf           := fun a b =>
    ⟨Lattice.inf a.fst b.fst, Lattice.inf a.snd b.snd⟩
  sup           := fun a b =>
    ⟨Lattice.sup a.fst b.fst, Lattice.sup a.snd b.snd⟩
  inf_le_left   := fun a b => ⟨Lattice.inf_le_left a.fst b.fst,
                                Lattice.inf_le_left a.snd b.snd⟩
  inf_le_right  := fun a b => ⟨Lattice.inf_le_right a.fst b.fst,
                                Lattice.inf_le_right a.snd b.snd⟩
  le_inf        := fun a b c hyp₁ hyp₂ =>
    ⟨Lattice.le_inf a.fst b.fst c.fst hyp₁.left hyp₂.left,
     Lattice.le_inf a.snd b.snd c.snd hyp₁.right hyp₂.right⟩
  sup_le_left   := fun a b => ⟨Lattice.sup_le_left a.fst b.fst,
                                Lattice.sup_le_left a.snd b.snd⟩
  sup_le_right  := fun a b => ⟨Lattice.sup_le_right a.fst b.fst,
                                Lattice.sup_le_right a.snd b.snd⟩
  le_sup        := fun a b c hyp₁ hyp₂ =>
    ⟨Lattice.le_sup a.fst b.fst c.fst hyp₁.left hyp₂.left,
     Lattice.le_sup a.snd b.snd c.snd hyp₁.right hyp₂.right⟩

-- Exercise 6.1 (three-cell multiplication constraint)
namespace Propagators

def mulProp (cx cy cz : Cell FlatNat) : PropStep := do
  let x ← cx.read
  let y ← cy.read
  match x, y with
    | .known a, .known b => cz.write (.known (a * b))
    | _,        _        => return false

def divProp (cz cx cy : Cell FlatNat) : PropStep := do
  let z ← cz.read
  let x ← cx.read
  match z, x with
    | .known z, .known x =>
      if x ∣ z then cy.write (.known (z / x))
               else cy.write (.conflict)
    | _, _ => return false

def mulNetwork : IO Unit := do
  let cx ← Cell.new (α := FlatNat)
  let cy ← Cell.new (α := FlatNat)
  let cz ← Cell.new (α := FlatNat)

  let _ ← cx.write (.known 3)
  let _ ← cz.write (.known 12)

  let net : Network := Network.mk #[
    mulProp cx cy cz,
    divProp cz cx cy,   -- z / x → y
    divProp cz cy cx    -- z / y → x
  ]
  net.run

  let yVal ← cy.read
  match yVal with
    | .known n  => IO.println s!"y = {n}"   -- y = 4  ✓ verified
    | .unknown  => IO.println "y is unknown"
    | .conflict => IO.println "contradiction"

#eval mulNetwork   -- y = 4  ✓ verified

-- Exercise 6.2 (conflict detection)
def conflictExample : IO Unit := do
  let cx ← Cell.new (α := FlatNat)

  -- Two independent sources disagree about x
  let _ ← cx.write (.known 3)
  let _ ← cx.write (.known 5)

  let xVal ← cx.read
  match xVal with
    | .conflict => IO.println "contradiction (expected)"
    | .known n  => IO.println s!"x = {n}"
    | .unknown  => IO.println "x unknown"

#eval conflictExample   -- contradiction (expected)  ✓ verified

-- To demonstrate downstream propagation, add a dependent cell.
-- Because addProp wraps the pure addFn — which maps conflicted
-- inputs to conflict — the contradiction in cx reaches csum.
def conflictPropagates : IO Unit := do
  let cx   ← Cell.new (α := FlatNat)
  let cy   ← Cell.new (α := FlatNat)
  let csum ← Cell.new (α := FlatNat)

  let _ ← cx.write (.known 3)
  let _ ← cx.write (.known 5)   -- cx is now conflict
  let _ ← cy.write (.known 7)

  let net : Network := Network.mk #[addProp cx cy csum]
  net.run

  let s ← csum.read
  match s with
    | .conflict => IO.println "sum is conflict (expected)"
    | .known n  => IO.println s!"sum = {n}"
    | .unknown  => IO.println "sum unknown"

#eval conflictPropagates   -- sum is conflict (expected)  ✓ verified

end Propagators
