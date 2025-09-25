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


/-- 可換環: ab = ba が成り立つ環 -/
class CommRing' (α : Type) extends Ring' α where
  /-- ab = ba -/
  mul_comm : ∀ a b, mul a b = mul b a


/-- 可除環(division ring) -/
class DivisionRing' (α : Type) extends Ring' α where
  /-- 1 ≠ 0 、つまり零環ではない -/
  one_ne_zero : one ≠ zero

  /-- a⁻¹ -/
  inv : α → α

  /--
  a ≠ 0 が乗法ｎ関して可逆元
  すべての元 a が 0 ではないならば、 a⁻¹ * a = 1 (つまり、可逆元になれる)
  -/
  mul_inv : ∀ a, a ≠ Ring'.zero → Ring'.mul a (inv a) = Ring'.one

  /-
  inv : α
  にして、
  mul_inv を
  ...  → Ring'.mul a inv ...
  にしてもいいのではないかと思ったが、
  それだと a⁻¹ が1つしか存在しない(どの元に対しても同じ1つの単元をかけて1になる)ことになるので、おかしい
  -/
