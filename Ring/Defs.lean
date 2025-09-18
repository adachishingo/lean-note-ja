import Mathlib.Logic.Function.Defs

/-- 環の定義 -/
class Ring' (α : Type) where
  /-- 和 -/
  add : α → α → α

  /-- + の単位元 0 -/
  zero : α

  /-- 積 -/
  mul : α → α → α

  /-- 和に関してアーベル群 -/
  add_com : ∀ a b, add a b = add b a

  /- (ab)c = a(bc) -/
  cal_assoc : ∀ a b c, mul (mul a b) c = mul a (mul b c)

  /-- 分配法則 -/
  distrib_left : ∀ a b c, mul a (add b c) = add (mul a b) (mul a c)

  /-- * の単位元 1 -/
  one : α

  /- a1 = a -/
  mul_one : ∀ a, mul a one = a

  /- 1a = a -/
  one_mul : ∀ a, mul one a = a

  /- ab = ba -/
  cal_comm : ∀ a b, mul a b = mul b a

  /- aa⁻¹ = e -/
  inv : ∀ a, ∃ b, mul a b = one

infixl:65 " + " => Ring'.add
infixl:70 " * " => Ring'.mul
