import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.Subgroup.Defs -- Subgroup
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Nat.Find
import Mathlib.Data.Set.Defs

/-!
# 群

群の定義
置換
置換群
互換
巡回置換
部分群
生成元
生成される部分群
群の直積
準同型
同型
自己同型
内部自己同型
共役
同値関係
剰余類
左剰余類
両側剰余類
正規部分群

-/


/-! ### 群の定義 -/

/-- 群の定義 -/
class Group' (α : Type) where
  /-- 演算 -/
  mul : α → α → α

  /-- 単位元 ae = ea = a となる e -/
  one : α

  /-- ea = a -/
  one_mul : ∀ a, mul one a = a

  /-- ae = a -/
  mul_one : ∀ a, mul a one = a

  /- 逆元 aa⁻¹ = e -/
  inv : ∀ a, ∃ b, mul a b = one

  /- 結合法則 : (ab)c = a(bc) -/
  cal_assoc : ∀ a b c, mul (mul a b) c = mul a (mul b c)


/- ライブラリーに、群を表す `Group` が定義されているので、以降は `Group` を使います。 -/


/- 位数 -/
-- TODO

/-- 置換: X から X への全単射写像 -/
structure Perm (α : Type) where
  f : α → α -- 写像
  bij : Function.Bijective f -- 写像 f は全単射

/-- 置換群: Xの置換全体からなる群 -/
instance permGroup {α : Type} : Group (Perm α) where
  -- TODO: 証明を書く
  mul := sorry
  one := sorry
  mul_one := sorry
  one_mul := sorry
  inv := sorry
  inv_mul_cancel := sorry
  npow_zero := sorry
  npow_succ := sorry
  div_eq_mul_inv := sorry
  mul_assoc := sorry

/-- 互換: 置換 σ が l ≠ i, j なら σ(l)=l で、それ以外は σ(i)=j, σ(j)=i -/
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
  -- TODO: 証明を書く
  f := sorry,
  bij := sorry  -- 全単射の証明
}


/-! ### 部分群 -/

/-- 部分群 -/
structure Subgroup' (G : Type) [Group G] where
  carrier : Set G
  -- 部分群の元 a, b に対して、 a * b も元
  -- A ∧ B → C を、 A → B → C という書き方をすることがあるようです。
  mul_mem {a b : G} : a ∈ carrier → b ∈ carrier → a * b ∈ carrier 
  one_mem : 1 ∈ carrier -- 単位元がある
  inv_mem {x : G} : x ∈ carrier → x⁻¹ ∈ carrier -- 逆元がある


/- ライブラリーに `Subgroup` があるので以降は `Subgroup` を使用します。 -/


/-!
### 生成元

- word
- 生成される部分群
-/

/-- a または a⁻¹ を明示する型（S の元に限定） -/
inductive GenWithInv {α : Type} (S : Set α) : Type
  | of  : (a : α) → (h : a ∈ S) → GenWithInv S
  | inv : (a : α) → (h : a ∈ S) → GenWithInv S

/-- S の元だけからなる語 -/
def word {α : Type} (S : Set α) : Type :=
  List (GenWithInv S)

/--
word を評価して群の元を得る

word の時点では、かけ算の列であって、 G の元ではないから、
x₁¹x₁⁻¹...xₙ¹xₙ⁻¹ を計算しないといけないです。
-/
def evalWords {α : Type} [Group α] {S : Set α} : word S → α
  /- 先頭から値をひとつずつ取り出しながら、再帰的に全部の要素をかける -/
  | [] => 1 -- 長さが 0 なら単位元
  -- 値が元の場合、 a * (残りのリストの計算結果(evalWords w))
  -- a :: w : 先頭の値 a と、残りのリスト w に分ける
  | GenWithInv.of a _ :: w => a * (evalWords w)
  -- 値が単位元の場合、 a⁻¹ * 残りのリストの計算結果
  | GenWithInv.inv a _ :: w => a⁻¹ * (evalWords w)

/-- S によって生成される部分群の台集合 -/
def SubgroupGeneratedBy {α : Type} [Group α] (S : Set α) : Set α :=
  -- 集合から得られる word が、
  -- 部分集合 S の元だけからできている word の集合
  { x | ∃ w : word S, evalWords w = x }

/-- 1つの元 g から生成される部分群の集合 -/
def CyclicSubgroupGeneratedBy {α : Type} [Group α] (g : α) : Set α :=
  -- {g}: gだけの集合
  SubgroupGeneratedBy {g}

/-- α が巡回群であるとは、ある g によって α 全体が生成されること -/
def IsCyclic' {α : Type} [Group α] : Prop :=
  ∃ g : α, CyclicSubgroupGeneratedBy g = (Set.univ : Set α)

/-- 群の直積 -/
def GroupProd (I : Type) (G : I → Type) [∀ i, Group (G i)] : Type :=
  (i : I) → G i  -- 各 i に対して G i の元を割り当てる関数（直積）

/-- 群にべき乗を定義 -/
def pow {α : Type} [Group α] (x : α) : ℕ → α
  | 0 => 1
  | n + 1 => x * (x ^ n)


/-! ## 位数 -/

/-- 条件に一致する -/
def listFind? {α : Type} (p : α → Bool) : List α → Option α
  | [] => none
  | x :: xs => if p x then some x else listFind? p xs

/-- 位数 -/
def order {α : Type} [Group α] [DecidableEq α] (x : α) (maxN : ℕ) : Option ℕ :=
  let check (n : ℕ) := n ≠ 0 ∧ x ^ n = 1
  listFind? check (List.range (maxN + 1))


/-! ### 準同型、同型 -/

/-- 準同型 -/
structure Hom {G₁ G₂ : Type} [Group G₁] [Group G₂] (φ : G₁ → G₂) where
  toFun := φ
  hom : ∀ x y: G₁, toFun (x * y) = toFun x * toFun y

/-- 核 -/
def ker {G₁ G₂ : Type} [Group G₁] [Group G₂] (φ : G₁ → G₂) : Set G₁ :=
  { x | φ x = 1 }

/-- 像 -/
def Im {G₁ G₂ : Type} [Group G₁] [Group G₂] (φ : G₁ → G₂) : Set G₂ :=
  { φ x | x : G₁ }

/-- 同型 -/
structure Iso {G₁ G₂ : Type} [Group G₁] [Group G₂] (φ : G₁ → G₂) where
  hom : Hom φ
  invFun : G₂ → G₁
  left_inv : ∀ x : G₁, invFun (φ x) = x
  right_inv : ∀ y : G₂, φ (invFun y) = y
  inv_hom : Hom invFun

/-- 自己同型 -/
structure AutoIso {G : Type} [Group G] (φ : G → G) where
  iso : Iso φ

/-- 自己同型全体の集合 -/
structure Aut (G : Type) [Group G] where
  toFun : G → G
  autoIso : AutoIso toFun

/-- Aut を Σ を使って Type として定義する場合 -/
def Aut' (G : Type) [Group G] : Type :=
  Σ φ : G → G, AutoIso φ

-- 下記ではエラーになりました。
-- def Aut'' (G : Type) [Group G] : Type := { φ // AutoIso φ }

/-- Aut G が群になる -/
instance {G : Type} [Group G] : Group (Aut G) where
  -- TODO: 証明を書く
  mul  := sorry
  one := sorry
  inv := sorry
  mul_assoc := sorry
  one_mul := sorry
  mul_one := sorry
  inv_mul_cancel := sorry

/--
ig
ig(h) = ghg⁻¹
-/
def ig {G : Type} [Group G] (g : G) : G → G :=
  fun h => g * h * g⁻¹

/-- 内部自己同型 -/
def innerAutoIso {G : Type} [Group G] (g : G) : AutoIso (ig g) :=
  -- TODO: 証明を書く
  {
    iso :=
    {
      hom := sorry
      invFun := ig g⁻¹
      left_inv := sorry
      right_inv := sorry
      inv_hom := sorry
    }
  }

-- こういう風に、 instance にはしないものらしい
-- instance {G : Type} [Group G] (g : G) : AutoIso (ig g) where
--   iso := sorry

/-- 共役 : 群 G の元 g による共役作用 -/
def conjugation {G : Type} [Group G] (h₁ h₂ : G) : Prop :=
  ∃ g, h₁ = ig g h₂

/-- 共役を structure として定義した場合 -/
structure Conjugate {G : Type} [Group G] (h₁ h₂ : G) : Prop where
  h : conjugation h₁ h₂

/- 写像 φ
φ : G → Aut G
φ(g) = ig
-/
def φ {G : Type} [Group G] : G → Aut G :=
  fun g => {
    toFun := ig g,
    autoIso := innerAutoIso g
  }

/-- 例: 上の φ は準同型である -/
-- φ は、 (φ : G → Aut G) にしないとエラー(typeclass instance problem is stuck, it is often due to metavariables)になった
def phi_hom {G : Type} [Group G] : Hom (φ : G → Aut G) :=
{
  -- TODO: 証明を書く
  hom := sorry
}

/--
内部自己同型群
上の φ について、 Im(φ) ⊆ Aut G を内部自己同型群といい、 Inn Gと書く
-/
def Inn (G : Type) [Group G] : Set (Aut G) :=
  Im φ


/-! ## 同値関係、剰余類 -/

/-- 同値関係 -/
structure Equivalence' {α : Type} (r : α → α → Prop) where
  refl : ∀ a, r a a -- 反射律
  symm : ∀ a b, r a b → r b a -- 対象律
  trans : ∀ a b c, r a b → r b c → r a c -- 推移律

/-- 例: x = y という関係 -/
def x_eq_y {α : Type} [Group α] : α → α → Prop :=
  fun x y => x = y

/- 例: x = y を同値関係にしてみる -/
instance EqEquiv' {α : Type} [Group α] : Equivalence' (@x_eq_y α _ ) where
  -- TODO: 証明を書く
  refl := sorry
  symm := sorry
  trans := sorry

/- `Equivalence` が定義されているので、以降は `Equivalence` を使います。 -/

/-
同値関係 - 同値類 - 商について

条件を満たす関係 ⇒ 同値関係

同値類 : xと同値関係で同じになる値の集合
(例: 「2で割った余りが同じ」という同値関係の場合、2の同値類は{2, 4, 6, ...})

同値類の集合 ⇒ 商
(例: {1, 3, 5, ...}, {2, 4, 6, ...})

-/

/-- mathlibでは、同値関係を表すのに、Equivalenceというものを使う -/
instance EqEquiv {α : Type} [Group α] : Equivalence (@x_eq_y α _) where
  refl := sorry
  symm := sorry
  trans := sorry

/-- mathlibでは、同値関係をもつ集合をSetidというものを使う -/
instance SetoidInvXYOne {α : Type} [Group α] : Setoid α where
  r := x_eq_y -- r : 同値関係
  iseqv := EqEquiv -- 同値関係の証明

/-- mathlibでは、商集合を表すのに、Quitientというものを使う -/
def quotient_inv_x_y_one {α : Type} [Group α] := Quotient (SetoidInvXYOne : Setoid α)

/--
つまり、同値関係による商は
同値関係による商集合（Quotient）の型構成子
-/
def quotient_by {α : Type} (r : α → α → Prop) (h : Equivalence r): Type :=
  Quotient { r := r, iseqv := ‹Equivalence r› }

/-
同値関係 - 同値類 - 商が、それぞれライブラリーでどう表されているか

同値関係: Equivalence
↓
同値関係を持つ集合: Setoid
↓
同値類: Quotient
-/

/-- S から S/~ への自然な写像 -/
def proj {α : Type} (r : α → α → Prop) (h : Equivalence r) : α → Quotient (Setoid.mk r h) :=
  fun a => Quotient.mk (Setoid.mk r h) a


/-! ### 左剰余類 -/

/-- x⁻¹ * y ∈ H という関係 -/
def left_rel {G : Type} [Group G] (H : Subgroup G) (x y : G) : Prop :=
  x⁻¹ * y ∈ H

/-- x⁻¹ * y ∈ H は同値関係 -/
def left_rel_equiv {G : Type} [Group G] (H : Subgroup G) : Equivalence (left_rel H) :=
{
  refl := by
    intro h
    rw [left_rel]
    rw [inv_mul_cancel]
    apply one_mem
  ,
  -- TODO: 証明を書く
  symm := by
    intro h h2 h3
    rw [left_rel]
    rw [left_rel] at h3
    sorry
  ,
  -- TODO: 証明を書く
  trans := sorry
}

/-- 同値類を作るために、 x⁻¹ * y ∈ H の Setoid を作る -/
def left_rel_setoid  {G : Type} [Group G] (H : Subgroup G) : Setoid G :=
{
    r := left_rel H,
    iseqv := left_rel_equiv H
}

/-- 同値類 -/
def left_coset_class {G : Type} [Group G] (H : Subgroup G)  (x : G) : Quotient (left_rel_setoid H) :=
  Quotient.mk'' x

/-- 同値類 (⟦⟧を使った記法) -/
def left_coset_class' {G : Type} [Group G] (H : Subgroup G)  (x : G) : Quotient (left_rel_setoid H) :=
  ⟦x⟧

/-- この同値関係による商 つまり 左剰余類の集合 -/
def left_coset_set {G : Type} [Group G] (H : Subgroup G) : Type := Quotient (left_rel_setoid H)


/-! ### 指数 -/

/-- 指数を定義するため、GとHが有限の場合を定義 -/
instance fintype_left_coset_set {G : Type} [Group G] [Fintype G] (H : Subgroup G) [Fintype (↥H)] :
  Fintype (left_coset_set H) := sorry -- TODO: 証明を書く

/-- 指数 : G/Hの元の個数 -/
def index {G : Type} [Group G] [Fintype G] (H : Subgroup G) [Fintype (↥H)] : ℕ :=
  Fintype.card (left_coset_set H)


/-! ### 両側剰余類 -/

/-- 両側剰余類の関係 -/
def double_coset_rel {G : Type} [Group G] (H K : Subgroup G) (g₁ g₂ : G) : Prop :=
  ∃ h ∈ H, ∃ k ∈ K, g₁ = h * g₂ * k

/-- これは同値関係 -/
def double_coset_equiv {G : Type} [Group G] (H K : Subgroup G) : Equivalence (double_coset_rel H K) :=
  sorry -- TODO: 証明を書く

/-- Setoid -/
def double_coset_setoid  {G : Type} [Group G] (H K : Subgroup G) : Setoid G :=
{
    r := double_coset_rel H K,
    iseqv := double_coset_equiv H K
}

/-- Setoid (⟨⟩ を使った記法) -/
def double_coset_setoid' {G : Type} [Group G] (H K : Subgroup G) : Setoid G :=
  ⟨double_coset_rel H K, double_coset_equiv H K⟩

/-- 両側剰余類 -/
def double_coset_class {G : Type} [Group G] (H K: Subgroup G) (x : G) : Quotient (double_coset_setoid H K) :=
  Quotient.mk (double_coset_setoid H K) x

/-- 同値関係による商、つまり両側剰余類の集合 -/
def double_coset {G : Type} [Group G] (H K : Subgroup G) : Type := Quotient (double_coset_setoid H K)


/-! ### 正規部分群 -/

/-- 正規部分群 -/
def is_normal_subgroup {G : Type} [Group G] (H : Subgroup G) : Prop :=
  ∀ g : G, ∀ h ∈ H, g * h * g ⁻¹ ∈ H
