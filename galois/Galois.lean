class Group (G: Type) where
  mul         : G → G → G
  one         : G
  inv         : G → G
  mul_assoc   : ∀ (a b c : G), mul (mul a b) c = mul a (mul b c)
  mul_one     : ∀ a : G, mul a one = a
  one_mul     : ∀ a : G, mul one a = a
  mul_inv     : ∀ a : G, mul a (inv a) = one
  inv_mul     : ∀ a : G, mul (inv a) a = one

instance {G : Type} [Group G] : Mul G where mul := Group.mul
instance {G : Type} [Group G] : One G where one := Group.one
instance {G : Type} [Group G] : Inv G where inv := Group.inv

instance : Group Int where
mul := (· + ·)
one := 0
inv := (- ·)
mul_assoc := Int.add_assoc
mul_one := Int.add_zero
one_mul := Int.zero_add
mul_inv := Int.add_right_neg
inv_mul := Int.add_left_neg
