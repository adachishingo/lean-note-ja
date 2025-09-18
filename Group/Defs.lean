import Mathlib.Logic.Function.Defs

/-- 群の定義 -/
class Group' (α : Type) where
  /-- 演算 -/
  mul : α → α → α

  /-- 単位元 ae = ea = a -/
  one : α

  /- ae = a -/
  mul_one : ∀ a, mul a one = a

  /- ea = a -/
  one_mul : ∀ a, mul one a = a

  /- ab = ba -/
  cal_comm : ∀ a b, mul a b = mul b a

  /- aa⁻¹ = e -/
  inv : ∀ a, ∃ b, mul a b = one

  /- (ab)c = a(bc) -/
  cal_assoc : ∀ a b c, mul (mul a b) c = mul a (mul b c)

/-- 置換: X から X への全単射写像 -/
structure Perm (α : Type) where
  f : α → α -- 写像
  bij : Function.Bijective f -- 写像 f は全単射

/-- 置換群: Xの置換全体からなる群 -/
instance permGroup {α : Type} : Group' (Perm α) where
  mul := sorry
  one := sorry
  mul_one := sorry
  one_mul := sorry
  cal_comm := sorry
  inv := sorry
  cal_assoc := sorry

/-- 互換: 置換 σ が l≠i,j なら σ(l)=l で σ(i)=j, σ(j)=i -/
def swap {α : Type} [DecidableEq α] (a b : α) : Perm α :=
{
  f := fun x =>
    if x = a then b
    else if x = b then a
    else x,
  bij := sorry
}

/-- 巡回置換 -/
def cycle_perm {α : Type} [DecidableEq α] (m : ℕ) (cycle : List α) : Perm α :=
{
  f := sorry, -- TODO
  bij := sorry  -- 全単射の証明
}
