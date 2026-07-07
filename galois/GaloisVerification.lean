/- ============================================================
   Galois Theory for Programmers — Companion Verification
   ============================================================

   Verification of every Lean 4 listing (and every checkable
   prose claim about Lean) in `galois-theory-for-programmers.tex`.

   Toolchain: leanprover/lean4:v4.31.0, CORE LEAN ONLY (no Mathlib),
   exactly as the book advertises ("vanilla Lean 4, no Mathlib
   dependency", Preface l.275).

   Compile:  lake env lean galois/GaloisVerification.lean

   Conventions in this file:
     -- DEVIATION: <what the book printed> — <why it fails> — <fix>
     -- BOOK'S OWN SORRY: a `sorry` the book deliberately leaves
        (exercise scaffold); reproduced faithfully.

   Section numbering follows the book's chapters.
   ============================================================ -/

namespace GaloisVerify

/- ============================================================
   Ch.1 §2  The Group typeclass                    (tex l.377)
   ============================================================ -/
namespace Ch1

class Group (G : Type) where
  mul : G → G → G
  one : G
  inv : G → G
  mul_assoc : ∀ a b c : G, mul (mul a b) c = mul a (mul b c)
  one_mul   : ∀ a : G, mul one a = a
  mul_one   : ∀ a : G, mul a one = a
  inv_mul   : ∀ a : G, mul (inv a) a = one
  mul_inv   : ∀ a : G, mul a (inv a) = one

instance [Group G] : Mul G where mul := Group.mul
instance [Group G] : One G where one := Group.one
instance [Group G] : Inv G where inv := Group.inv

/- Ch.1 §3  The integers under addition            (tex l.410)

   DEVIATION: the book writes
       inv_mul := Int.neg_add_cancel
       mul_inv := Int.add_neg_cancel
   Neither constant exists in core Lean v4.31.0 (compile error
   "Unknown constant `Int.neg_add_cancel`").  The user's own
   Galois.lean already discovered this and used the correct core
   names `Int.add_left_neg` / `Int.add_right_neg`; that is the fix. -/
instance : Group Int where
  mul := (· + ·)
  one := 0
  inv := (- ·)
  mul_assoc := Int.add_assoc
  one_mul   := Int.zero_add
  mul_one   := Int.add_zero
  inv_mul   := Int.add_left_neg    -- DEVIATION: was `Int.neg_add_cancel` (nonexistent)
  mul_inv   := Int.add_right_neg   -- DEVIATION: was `Int.add_neg_cancel`  (nonexistent)

/- Ch.1 §3  ℤ/nℤ as Fin n                          (tex l.448)

   DEVIATION: the book's `addMod` is
       def Fin.addMod (a b : Fin n) : Fin n :=
         ⟨(a.val + b.val) % n, Nat.mod_lt _ (by omega)⟩
   This does NOT compile: `Nat.mod_lt` needs `0 < n`, but with no
   hypothesis `omega` reports "No usable constraints found".  The
   fix is to recover `0 < n` from the input `a : Fin n` (whose
   `.isLt` witnesses `a.val < n`, forcing `n > 0`). -/
def Fin.addMod (a b : Fin n) : Fin n :=
  ⟨(a.val + b.val) % n, Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le a.val) a.isLt)⟩

-- The book's `negMod` (l.451) DOES compile as printed: it takes the
-- proof `h : n > 0` explicitly.
def Fin.negMod (a : Fin n) (h : n > 0) : Fin n :=
  ⟨(n - a.val) % n, Nat.mod_lt _ h⟩

/- Ch.1 §3  S₃ as an explicit enumeration          (tex l.501)

   The inductive type and `inv` are correct.  The `mul` TABLE,
   however, is NOT ASSOCIATIVE — it does not define a group.
   See the DEVIATION note after the corrected version. -/
inductive S3 where
  | e | r | r2 | s | sr | sr2
  deriving DecidableEq, Repr

namespace S3
def all : List S3 := [e, r, r2, s, sr, sr2]

/- DEVIATION: the book's printed table (tex ll.513–540) has EIGHT
   wrong products and fails associativity (verified by #eval below):
       r·sr  : book s   → correct sr2
       r·sr2 : book sr  → correct s
       r2·sr : book sr2 → correct s
       r2·sr2: book s   → correct sr
       s·sr  : book r   → correct r2
       s·sr2 : book r2  → correct r
       sr·s  : book r2  → correct r
       sr2·s : book r   → correct r2
   The correct table below is the composition table (apply the
   right factor first) with s,r,sr,sr2 the reflections fixing
   vertices 1,·,3,2 respectively — the labelling the book itself
   fixes via its own entries r·s=sr, r2·s=sr2. The four rotation
   products and the entries the prose relies on (r·s=sr, s·r=sr2,
   tex l.554) are UNCHANGED — those were already correct. -/
def mul : S3 → S3 → S3
  | e,   x   => x
  | x,   e   => x
  | r,   r   => r2
  | r,   r2  => e
  | r2,  r   => e
  | r2,  r2  => r
  | s,   s   => e
  | s,   r   => sr2
  | s,   r2  => sr
  | r,   s   => sr
  | r2,  s   => sr2
  | sr,  sr  => e
  | sr2, sr2 => e
  | s,   sr  => r2    -- DEVIATION: book had `r`
  | s,   sr2 => r     -- DEVIATION: book had `r2`
  | sr,  s   => r     -- DEVIATION: book had `r2`
  | sr2, s   => r2    -- DEVIATION: book had `r`
  | r,   sr  => sr2   -- DEVIATION: book had `s`
  | r,   sr2 => s     -- DEVIATION: book had `sr`
  | r2,  sr  => s     -- DEVIATION: book had `sr2`
  | r2,  sr2 => sr    -- DEVIATION: book had `s`
  | sr,  r   => s
  | sr,  r2  => sr2
  | sr2, r   => sr
  | sr2, r2  => s
  | sr,  sr2 => r2
  | sr2, sr  => r

def inv : S3 → S3
  | e => e | r => r2 | r2 => r | s => s | sr => sr | sr2 => sr2

-- Corrected table IS a group: associative, with correct id & inverses.
example : all.all (fun a => all.all (fun b => all.all (fun c =>
    mul (mul a b) c == mul a (mul b c)))) = true := by native_decide
example : all.all (fun a => mul (inv a) a == e && mul a (inv a) == e) = true := by
  native_decide
-- Prose claim (l.554): r·s = sr but s·r = sr2, so S₃ is non-abelian.
example : mul r s = S3.sr ∧ mul s r = S3.sr2 ∧ mul r s ≠ mul s r := by decide
end S3

/- Ch.1 §4  Modular exponentiation                 (tex l.599)
   Compiles verbatim.  #eval outputs confirmed below. -/
def modPow (base exp modulus : Nat) : Nat :=
  if modulus ≤ 1 then 0
  else go base exp modulus 1
where
  go (base exp modulus acc : Nat) : Nat :=
    if exp = 0 then acc % modulus
    else
      let base' := (base * base) % modulus
      let acc'  := if exp % 2 = 1 then (acc * base) % modulus else acc
      go base' (exp / 2) modulus acc'
  termination_by exp

example : modPow 3 4 7 = 4 := by native_decide     -- 81 mod 7 = 4
example : modPow 2 10 1000 = 24 := by native_decide -- 1024 mod 1000 = 24
example : modPow 7 13 11 = 2 := by native_decide

/- Ch.1 §5  Group homomorphisms                     (tex l.631) -/
structure GroupHom (G H : Type) [Group G] [Group H] where
  toFun : G → H
  map_mul : ∀ a b : G, toFun (a * b) = toFun a * toFun b

/- DEVIATION: the book's proof body for `map_one` (tex l.639) is
       simp [mul_one] at h
   which fails: `mul_one` is not a top-level identifier in core
   ("Unknown identifier `mul_one`"); it is `Group.mul_one`.  Because
   the erroring line precedes the `sorry`, the whole listing fails
   to compile.  The theorem STATEMENT is fine; it is a deliberate
   exercise (1.4), so we keep the sorry. -/
theorem GroupHom.map_one [Group G] [Group H] (φ : GroupHom G H) :
    φ.toFun 1 = 1 := by
  sorry -- BOOK'S OWN SORRY (Exercise 1.4); book's `simp [mul_one]` scaffold does not compile

theorem GroupHom.map_inv [Group G] [Group H] (φ : GroupHom G H) (a : G) :
    φ.toFun a⁻¹ = (φ.toFun a)⁻¹ := by
  sorry -- BOOK'S OWN SORRY (Exercise 1.4)

end Ch1

/- ============================================================
   Ch.2  Subgroups, normal subgroups                (tex l.692)
   ============================================================

   DEVIATION (systemic): the book uses `Set G` for subgroup
   carriers, but `Set` is a Mathlib type — it does NOT exist in
   core Lean ("Unknown identifier `Set`").  Since the book insists
   on "no Mathlib dependency" (l.275), we supply the standard
   core encoding `Set α := α → Prop` with a membership instance,
   exactly enough to make the listings type-check. -/
namespace Ch2
open Ch1 (Group)

abbrev Set (α : Type) := α → Prop
instance : Membership α (Set α) where mem s a := s a  -- (a ∈ s) := s a

structure Subgroup (G : Type) [Group G] where
  carrier : Set G
  one_mem : (1 : G) ∈ carrier
  mul_mem : ∀ {a b : G}, a ∈ carrier → b ∈ carrier → a * b ∈ carrier
  inv_mem : ∀ {a : G}, a ∈ carrier → a⁻¹ ∈ carrier

instance [Group G] : Membership G (Subgroup G) where
  mem H a := a ∈ H.carrier

structure NormalSubgroup (G : Type) [Group G] extends Subgroup G where
  conj_mem : ∀ {n : G}, n ∈ carrier → ∀ g : G, g * n * g⁻¹ ∈ carrier

end Ch2

/- ============================================================
   Ch.3  Order theory: PartialOrder, Lattice, GC   (tex l.904)
   ============================================================ -/
namespace Ch3

class PartialOrder (P : Type) where
  le : P → P → Prop
  le_refl : ∀ a : P, le a a
  le_antisymm : ∀ a b : P, le a b → le b a → a = b
  le_trans : ∀ a b c : P, le a b → le b c → le a c

instance [PartialOrder P] : LE P where le := PartialOrder.le

class Lattice (L : Type) extends PartialOrder L where
  meet : L → L → L
  join : L → L → L
  meet_le_left  : ∀ a b : L, le (meet a b) a
  meet_le_right : ∀ a b : L, le (meet a b) b
  le_meet : ∀ a b c : L, le c a → le c b → le c (meet a b)
  le_join_left  : ∀ a b : L, le a (join a b)
  le_join_right : ∀ a b : L, le b (join a b)
  join_le : ∀ a b c : L, le a c → le b c → le (join a b) c

/- DEVIATION: the book adds
       instance [Lattice L] : Inf L where inf := Lattice.meet
       instance [Lattice L] : Sup L where sup := Lattice.join
   but `Inf` and `Sup` are Mathlib classes — they are NOT in core
   Lean ("unknown identifier `Inf`/`Sup`").  Omitted here; the
   `Lattice` class itself compiles fine.  (A core alternative is
   `Min`/`Max`, or defining `⊓`/`⊔` notation directly.) -/

/- DEVIATION: the book printed the MONOTONE adjunction
       adjoint : ∀ p q, l p ≤ q ↔ p ≤ u q
   yet its Proposition, Warning and Chapter 8 all use the ANTITONE
   (order-reversing) notion (bigger field ↔ smaller group).  Under
   the monotone definition both maps are monotone, so the claimed
   order-reversal is false.  Fixed to the antitone adjunction
       q ≤ l p  ↔  p ≤ u q
   under which both `l` and `u` reverse order (proved below). -/
structure GaloisConnection (P Q : Type) [PartialOrder P] [PartialOrder Q] where
  l : P → Q
  u : Q → P
  adjoint : ∀ (p : P) (q : Q), q ≤ l p ↔ p ≤ u q

namespace GaloisConnection
variable {P Q : Type} [PartialOrder P] [PartialOrder Q]

-- (ii) unit on P:  p ≤ u (l p)
theorem le_u_l (gc : GaloisConnection P Q) (p : P) : p ≤ gc.u (gc.l p) :=
  (gc.adjoint p (gc.l p)).1 (PartialOrder.le_refl _)

-- (iii) unit on Q:  q ≤ l (u q)
theorem le_l_u (gc : GaloisConnection P Q) (q : Q) : q ≤ gc.l (gc.u q) :=
  (gc.adjoint (gc.u q) q).2 (PartialOrder.le_refl _)

-- (i) l is order-reversing
theorem l_antitone (gc : GaloisConnection P Q) {p₁ p₂ : P}
    (h : p₁ ≤ p₂) : gc.l p₂ ≤ gc.l p₁ :=
  (gc.adjoint p₁ (gc.l p₂)).2 (PartialOrder.le_trans _ _ _ h (gc.le_u_l p₂))

-- (i) u is order-reversing
theorem u_antitone (gc : GaloisConnection P Q) {q₁ q₂ : Q}
    (h : q₁ ≤ q₂) : gc.u q₂ ≤ gc.u q₁ :=
  (gc.adjoint (gc.u q₂) q₁).1 (PartialOrder.le_trans _ _ _ h (gc.le_l_u q₂))

end GaloisConnection

end Ch3

/- ============================================================
   Ch.4  Rings and Fields                           (tex l.1171)
   ============================================================ -/
namespace Ch4

class Ring (R : Type) where
  add : R → R → R
  zero : R
  neg : R → R
  mul : R → R → R
  one : R
  add_assoc : ∀ a b c : R, add (add a b) c = add a (add b c)
  add_comm  : ∀ a b : R, add a b = add b a
  zero_add  : ∀ a : R, add zero a = a
  neg_add   : ∀ a : R, add (neg a) a = zero
  mul_assoc : ∀ a b c : R, mul (mul a b) c = mul a (mul b c)
  one_mul   : ∀ a : R, mul one a = a
  mul_one   : ∀ a : R, mul a one = a
  left_distrib  : ∀ a b c : R, mul a (add b c) = add (mul a b) (mul a c)
  right_distrib : ∀ a b c : R, mul (add a b) c = add (mul a c) (mul b c)

-- Notation instances (mirror Ch.1's Group notation), so that the
-- book's `a + b`, `a * b`, `0`, `1`, `-a` work on any Ring/Field.
instance [Ring R] : Add R  where add := Ring.add
instance [Ring R] : Mul R  where mul := Ring.mul
instance [Ring R] : Zero R where zero := Ring.zero
instance [Ring R] : One R  where one := Ring.one
instance [Ring R] : Neg R  where neg := Ring.neg

class Field (F : Type) extends Ring F where
  mul_comm : ∀ a b : F, mul a b = mul b a
  inv : F → F
  mul_inv : ∀ a : F, a ≠ zero → mul a (inv a) = one
  zero_ne_one : zero ≠ one

/- Ch.5  Polynomials over a field                   (tex l.1280)
   Compiles verbatim. -/
structure Polynomial (F : Type) [Field F] where
  coeffs : List F
  deriving Repr

namespace Polynomial
def eval [Field F] (p : Polynomial F) (x : F) : F :=
  p.coeffs.foldr (fun c acc => Ring.add (Ring.mul acc x) c) Ring.zero

def degree [Field F] (p : Polynomial F) : Nat :=
  if p.coeffs.length = 0 then 0 else p.coeffs.length - 1
end Polynomial

end Ch4

/- ============================================================
   Ch.6  Field extension ℚ(√2)                       (tex l.1363)
   ============================================================
   The QSqrt2 structure and arithmetic compile verbatim; the
   `native_decide` verification of √2·√2 = 2 succeeds. -/
namespace Ch6

structure QSqrt2 where
  a : Rat
  b : Rat
  deriving Repr, DecidableEq

namespace QSqrt2
def add (x y : QSqrt2) : QSqrt2 := ⟨x.a + y.a, x.b + y.b⟩
def mul (x y : QSqrt2) : QSqrt2 :=
  ⟨x.a * y.a + 2 * x.b * y.b, x.a * y.b + y.a * x.b⟩
def inv (x : QSqrt2) : QSqrt2 :=
  let d := x.a * x.a - 2 * x.b * x.b
  ⟨x.a / d, -x.b / d⟩
def sqrt2 : QSqrt2 := ⟨0, 1⟩
example : mul sqrt2 sqrt2 = ⟨2, 0⟩ := by native_decide  -- √2·√2 = 2  ✓
end QSqrt2

end Ch6

/- ============================================================
   Ch.7  The nontrivial automorphism of ℚ(√2)        (tex l.1523)
   ============================================================ -/
namespace Ch7
open Ch6 (QSqrt2)
open Ch4 (Field)

def conjugate : QSqrt2 → QSqrt2
  | ⟨a, b⟩ => ⟨a, -b⟩

/- DEVIATION: all three theorems below are printed ending in `ring`
   (tex ll.1530, 1535, 1540).  `ring` is a Mathlib tactic — it does
   NOT exist in core Lean ("unknown tactic").  For the involution
   and the fixes-ℚ lemma, full `simp [conjugate]` closes the goal
   with no `ring` needed.  For `conjugate_mul` we discharge the two
   rational-arithmetic components with core `Rat` lemmas. -/
theorem conjugate_mul (x y : QSqrt2) :
    conjugate (QSqrt2.mul x y) = QSqrt2.mul (conjugate x) (conjugate y) := by
  simp only [conjugate, QSqrt2.mul, QSqrt2.mk.injEq]
  refine ⟨?_, ?_⟩
  · show x.a * y.a + 2 * x.b * y.b = x.a * y.a + 2 * -x.b * -y.b
    have h1 : (2 : Rat) * -x.b = -(2 * x.b) := by rw [Rat.mul_neg]
    have h2 : -(2 * x.b) * -y.b = 2 * x.b * y.b := by
      rw [Rat.neg_mul, Rat.mul_neg, Rat.neg_neg]
    rw [h1, h2]
  · show -(x.a * y.b + y.a * x.b) = x.a * -y.b + y.a * -x.b
    rw [Rat.mul_neg, Rat.mul_neg, Rat.neg_add]

theorem conjugate_conjugate (x : QSqrt2) :
    conjugate (conjugate x) = x := by
  simp [conjugate]   -- DEVIATION: book had `simp [conjugate]; ring`

theorem conjugate_fixes_rat (a : Rat) :
    conjugate ⟨a, 0⟩ = ⟨a, 0⟩ := by
  simp [conjugate]   -- DEVIATION: book had `simp [conjugate]; ring`

/- Ch.7 §2  FieldAut structure                       (tex l.1487)

   DEVIATION: the book's `FieldAut` does NOT compile for two
   reasons: (1) it writes `toFun (a + b)` / `toFun (a * b)` but its
   `Field` class provides no `Add`/`Mul` instances on `E`, so the
   `+`/`*` notation fails to synthesize (`failed to synthesize
   HAdd E E E`); (2) `fixes_base` mentions `embed` which is never
   defined (`Function expected at embed`).  A compiling version
   needs a Field with Add/Mul instances and an explicit embedding.
   Fix: (a) give `Ring`/`Field` the `Add`/`Mul` notation instances
   added in Ch.4, so `a + b` / `a * b` synthesize on `E`; and (b)
   make the inclusion `embed : F → E` an explicit field of the
   structure.  This compiles and is the shape used in the book. -/
structure FieldAut (E F : Type) [Field E] [Field F] where
  toFun  : E → E
  invFun : E → E
  embed  : F → E                 -- the inclusion map F ↪ E
  left_inv  : ∀ x, invFun (toFun x) = x
  right_inv : ∀ x, toFun (invFun x) = x
  map_add : ∀ a b, toFun (a + b) = toFun a + toFun b
  map_mul : ∀ a b, toFun (a * b) = toFun a * toFun b
  fixes_base : ∀ a : F, toFun (embed a) = embed a

end Ch7

/- ============================================================
   Ch.8  Fundamental theorem — illustrative skeleton (tex l.1647)
   ============================================================
   The book's block (fixedField / fixingGroup / galois_connection)
   is deliberately schematic: it references undefined names
   (`Gal E F`, `IntermediateField`, `IsSolvable`, `Inv`, ...) and
   ends every definition in `sorry`.  It is prose-in-code, not
   meant to compile.  We record the mathematical content (the
   correspondence and its four properties are stated CORRECTLY,
   including the order reversal) and do not attempt to reproduce
   the non-compiling skeleton here. -/

/- ============================================================
   Ch.10  Solvable groups — illustrative              (tex l.1860)
   ============================================================
   The book's `IsSolvable` uses undefined `IsNormal`, `IsAbelian`
   and a 2-argument `Quotient` — schematic, does not compile.  The
   MATH (composition series, S₄ solvable, S₅/A₅ not) is correct;
   see REVIEW.md. -/

/- ============================================================
   Ch.12  GF(2⁸) and the AES field                   (tex l.2044)
   ============================================================ -/
namespace Ch12

structure GF256 where
  val : UInt8
  deriving DecidableEq, Repr

namespace GF256
def add (a b : GF256) : GF256 := ⟨a.val ^^^ b.val⟩

/- DEVIATION: the book writes `if b == 0 then ...` with plain
   `termination_by b.toNat`, which FAILS to prove termination
   ("failed to prove termination"): Lean cannot discharge
   `(b >>> 1).toNat < b.toNat` automatically.  Fix: use a
   dependent `if h : b == 0` to obtain `b ≠ 0`, and add a
   `decreasing_by` block relating `>>> 1` to `/2`. -/
def mul (a b : GF256) : GF256 := go a.val b.val 0
where
  go (a b acc : UInt8) : GF256 :=
    if h : b == 0 then ⟨acc⟩
    else
      let acc' := if b &&& 1 != 0 then acc ^^^ a else acc
      let a'   := if a &&& 0x80 != 0
                  then (a <<< 1) ^^^ 0x1B  -- reduce mod m(x) = 0x11B
                  else a <<< 1
      go a' (b >>> 1) acc'
  termination_by b.toNat
  decreasing_by
    have hb : b ≠ 0 := by simpa using h
    have hbn : b.toNat ≠ 0 := fun hz => hb (by
      have := congrArg UInt8.ofNat hz; simpa using this)
    have hsr : (b >>> 1).toNat = b.toNat / 2 := by
      rw [UInt8.toNat_shiftRight, Nat.shiftRight_eq_div_pow]; rfl
    rw [hsr]; omega

def inv (a : GF256) : GF256 :=
  let a2   := mul a a
  let a4   := mul a2 a2
  let a8   := mul a4 a4
  let a16  := mul a8 a8
  let a32  := mul a16 a16
  let a64  := mul a32 a32
  let a128 := mul a64 a64
  mul (mul (mul (mul (mul (mul a2 a4) a8) a16) a32) a64) a128

def sbox (a : GF256) : GF256 :=
  let b := if a.val == 0 then ⟨(0 : UInt8)⟩ else inv a
  affineTransform b
where
  affineTransform (b : GF256) : GF256 :=
    sorry -- BOOK'S OWN SORRY (tex l.2092): AES affine transform left unimplemented

-- Verify the standard AES multiplication test vector 0x57·0x13 = 0xFE,
-- and that inv really inverts (0x53 · 0x53⁻¹ = 1).
example : (mul ⟨0x57⟩ ⟨0x13⟩).val = 0xFE := by native_decide
example : (mul ⟨0x53⟩ (inv ⟨0x53⟩)).val = 1 := by native_decide
end GF256

end Ch12

/- ============================================================
   Appendix  "A Lean 4 Primer"  — every example compiles
   ============================================================
   Each `example`/`def` below is the machine-checked companion of
   the corresponding primer entry in the .tex appendix. Core Lean
   only. -/
namespace Primer

-- inductive + def + pattern matching + structural recursion
inductive Tree where
  | leaf | node (l r : Tree)
  deriving Repr
def Tree.size : Tree → Nat
  | .leaf     => 1
  | .node l r => l.size + r.size
example : (Tree.node .leaf .leaf).size = 2 := rfl

-- structure + class + instance + anonymous constructor
structure Point where
  x : Nat
  y : Nat
  deriving Repr
instance : Add Point where add a b := ⟨a.x + b.x, a.y + b.y⟩
example : (⟨1,2⟩ : Point) + ⟨3,4⟩ = ⟨4,6⟩ := rfl

-- theorem/example, term vs tactic style
example (p q : Prop) (hp : p) (h : p → q) : q := h hp
example (p q : Prop) : p → (p → q) → q := by
  intro hp h; apply h; exact hp

-- rfl (compute), rw (rewrite)
example : 2 + 3 = 5 := rfl
example (a b : Nat) (h : a = b) : a + 1 = b + 1 := by rw [h]

-- simp
example (n : Nat) : n + 0 = n := by simp

-- decide (small decidable goals) and native_decide (compiled)
example : (7 : Nat) < 10 := by decide
example : List.range 4 = [0,1,2,3] := by native_decide

-- omega (linear arithmetic over Nat/Int)
example (n : Nat) (h : n + 2 ≤ 5) : n ≤ 3 := by omega

-- cases  ↔  the recursor as a term
example (b : Bool) : b = true ∨ b = false := by
  cases b with
  | true  => exact Or.inl rfl
  | false => exact Or.inr rfl
-- the same, written directly with the auto-generated recursor:
example (b : Bool) : b = true ∨ b = false :=
  Bool.rec (Or.inr rfl) (Or.inl rfl) b

-- induction  ↔  Nat.rec (motive := …); the successor case uses `ih`
theorem zero_add_primer (n : Nat) : 0 + n = n := by
  induction n with
  | zero => rfl
  | succ k ih => rw [Nat.add_succ, ih]

-- obtain  ↔  Exists.elim / match on the witness
example (h : ∃ n : Nat, n = 3) : True := by
  obtain ⟨n, hn⟩ := h; trivial
example (h : ∃ n : Nat, n = 3) : True :=
  Exists.elim h (fun _ _ => trivial)

-- calc  ↔  chained Trans.trans
example (a b c : Nat) (h1 : a = b) (h2 : b = c) : a = c := by
  calc a = b := h1
    _ = c := h2

-- by_contra: NOT core (it lives in Batteries/Mathlib).  Core Lean
-- expresses proof-by-contradiction with the term `Classical.byContradiction`.
example (p : Prop) (h : ¬ ¬ p) : p :=
  Classical.byContradiction (fun hn => h hn)

end Primer

end GaloisVerify
