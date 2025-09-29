import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.Subgroup.Defs -- Subgroup
import Mathlib.Data.Fintype.Card
import Mathlib.GroupTheory.QuotientGroup.Defs
-- import Mathlib.Data.Fintype.Defs
-- import Mathlib.Data.Nat.Find
-- import Mathlib.Data.Set.Defs
-- import Mathlib.Order.TypeTags

/-!
# 群

## 群の定義

群の定義
置換
置換群
互換
巡回置換

## 部分群

部分群
生成元
生成される部分群
群の直積

## 準同型

準同型
同型
自己同型
内部自己同型
共役

## 同値関係、剰余類

同値関係
剰余類
左剰余類
両側剰余類

## 正規部分群

正規部分群

## 準同型定理

準同型定理
-/


/-! ### 群の定義 -/

/-- 群(group)の定義 -/
class Group' (α : Type) where
  /-- 演算 -/
  mul : α → α → α

  /-- 単位元(unit) ae = ea = a となる e -/
  one : α

  /-- ea = a -/
  one_mul : ∀ a, mul one a = a

  /-- ae = a -/
  mul_one : ∀ a, mul a one = a

  /- 逆元(inverse) aa⁻¹ = e -/
  inv : ∀ a, ∃ b, mul a b = one

  /- 結合(associative)法則 : (ab)c = a(bc) -/
  mul_assoc : ∀ a b c, mul (mul a b) c = mul a (mul b c)


/- ライブラリーに、群を表す `Group` が定義されているので、以降は `Group` を使います。 -/

/- 位数(order) -/
-- TODO

/- 自明な群 G = {e}
ee = e と定義すると、群になる
-/

/- 群にべき乗(power)を定義 -/
-- def pow {α : Type} [Group α] (x : α) : ℕ → α
--   | 0 => 1
--   | n + 1 => x * (x ^ n)


/-! ### 置換 -/

/-- 置換(permutation): X から X への全単射写像 -/
structure Perm (α : Type) where
  f : α → α -- 写像
  bij : Function.Bijective f -- 写像 f は全単射

/-- 置換群(permutation group): Xの置換全体からなる群 -/
instance instPermGroup {α : Type} : Group (Perm α) where
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

/-- 互換(transposition): σ(i)=j, σ(j)=i で、それ以外は変えない置換 -/
def swap {α : Type} [DecidableEq α] (a b : α) : Perm α :=
{
  f := fun x =>
    if x = a then b
    else if x = b then a
    else x,
  bij := sorry
}

/-- 長さ m の巡回置換(cyclic permutation): i₁→i₂, i₂→i₃, ... iₘ→i₁ と移して、他は変えない置換 -/
def cyclePerm {α : Type} [DecidableEq α] (m : ℕ) (cycle : List α) : Perm α :=
{
  -- TODO: 証明を書く
  f := sorry,
  bij := sorry  -- 全単射の証明
}


/-! ### 部分群 -/

/-- 部分群(subgroup) -/
structure Subgroup' (G : Type) [Group G] where
  carrier : Set G
  -- 部分群の元 a, b に対して、 a * b も元
  -- A ∧ B → C を、 A → B → C という書き方をすることがあるようです。
  mul_mem {a b : G} : a ∈ carrier → b ∈ carrier → a * b ∈ carrier
  one_mem : 1 ∈ carrier -- 単位元がある
  inv_mem {x : G} : x ∈ carrier → x⁻¹ ∈ carrier -- 逆元がある


/- ライブラリーに `Subgroup` があるので以降は `Subgroup` を使用します。 -/


/-! ### 生成元

- 群 G の部分集合 S の word を定義
- 生成される部分群、を定義
  - word 全体の集合(⟨S⟩) = S によって生成された部分群
  - S = 生成系(system of generators)
  - S の元 = 生成元(generator)
-/

/- word を定義 -/

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

/- 生成される部分群 -/

/-- S によって生成される部分群の台集合 -/
def subgroupGeneratedBy {α : Type} [Group α] (S : Set α) : Set α :=
  -- 集合から得られる word が、
  -- 部分集合 S の元だけからできている word の集合
  { x | ∃ w : word S, evalWords w = x }

/-- 1つの元 g から生成される部分群の集合 -/
def cyclicSubgroupGeneratedBy {α : Type} [Group α] (g : α) : Set α :=
  -- {g}: gだけの集合
  subgroupGeneratedBy {g}

/-- α が巡回群(cyclic group)であるとは、ある g によって α 全体が生成されること -/
def IsCyclic' {α : Type} [Group α] : Prop :=
  ∃ g : α, cyclicSubgroupGeneratedBy g = (Set.univ : Set α)

/-- 群の直積(direct product)
教科書では、
有限の場合 G₁ ⨯ ... ⨯ Gₜ
無限の場合 ΠGᵢ と書かれます -/
def GroupProd (I : Type) (G : I → Type) [∀ i, Group (G i)] : Type :=
  (i : I) → G i  -- 各 i に対して G i の元を割り当てる関数（直積）


/-! ### 位数 -/

-- TODO

-- /-- 条件に一致する最初の要素を取得 -/
-- def listFind {α : Type} (p : α → Bool) : List α → Option α
--   | [] => none
--   | x :: xs => if p x then some x else listFind p xs

-- /-- 位数: x ∈ G で xⁿ = 1G となる最小のもの、存在しない場合は ∞ -/
-- def order {α : Type} [Group α] [DecidableEq α] (x : α) (maxN : ℕ) : WithTop ℕ :=
--   let check (n : ℕ) := n ≠ 0 ∧ x ^ n = 1
--   match listFind check (List.range (maxN + 1)) with
--   | some n => n
--   | none   => ⊤


/-! ### 準同型 -/

/-- 準同型(homomorphism) -/
structure Hom (G₁ G₂ : Type) [Group G₁] [Group G₂] where
  -- 写像(φ)
  toFun : G₁ → G₂
  -- 写像(φ)が、 φ(xy) = φ(x)φ(y) を満たす = 準同型
  map_mul : ∀ x y: G₁, toFun (x * y) = toFun x * toFun y

/-- 核 -/
def Ker' {G₁ G₂ : Type} [Group G₁] [Group G₂] (φ : G₁ → G₂) : Set G₁ :=
  { x | φ x = 1 }

/-- 核 (部分群とする場合) -/
def Ker {G₁ G₂ : Type} [Group G₁] [Group G₂] (φ : G₁ → G₂) : Subgroup G₁ :=
{
  carrier := { x | φ x = 1 },
  mul_mem' := sorry,
  one_mem' := sorry,
  inv_mem' := sorry
}

/-- 像(image) -/
def Im' {G₁ G₂ : Type} [Group G₁] [Group G₂] (φ : G₁ → G₂) : Set G₂ :=
  { φ x | x : G₁ }

/-- 像 (部分群とする場合) -/
def Im {G₁ G₂ : Type} [Group G₁] [Group G₂] (φ : G₁ → G₂) : Subgroup G₂ :=
{
  carrier := { φ x | x : G₁},
  mul_mem' := sorry,
  one_mem' := sorry,
  inv_mem' := sorry
}

/-- 同型(isomorphism)
教科書では、 G₁ ≃ G₂ と書かれます -/
structure Iso (G₁ G₂ : Type) [Group G₁] [Group G₂] where
  hom : Hom G₁ G₂ -- G₁ G₂ は準同型
  invFun : G₂ → G₁ -- G₂ → G₁ の写像
  left_inv : ∀ x : G₁, invFun (hom.toFun x) = x -- toFun の 逆写像が invFun
  right_inv : ∀ y : G₂, hom.toFun (invFun y) = y -- invFun の 逆写像が toFun
  inv_hom : Hom  G₂ G₁ -- G₂ → G₁ は準同型

/-- 自己同型(automorphism) -/
structure Auto (G : Type) [Group G] where
  iso : Iso G G

/-- 自己同型全体の集合 -/
structure Aut (G : Type) [Group G] where
  toFun : G → G
  autoIso : Auto G

/-- Aut を Σ を使って Type として定義する場合 -/
def Aut' (G : Type) [Group G] : Type :=
  Σ _ : G → G, Auto G

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

/-- 内部自己同型(inner automorphism) -/
def innerAuto {G : Type} [Group G] (g : G) : Auto G :=
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

/-- 共役(conjugate) : 群 G の元 g による共役作用 -/
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
    autoIso := innerAuto g
  }

/-- 例: 上の φ は準同型である -/
-- φ は、 (φ : G → Aut G) にしないとエラー
-- (typeclass instance problem is stuck, it is often due to metavariables)になった
def phiHom {G : Type} [Group G] : Hom G (Aut G) :=
{
  -- TODO: 証明を書く
  toFun := sorry,
  map_mul := sorry
}

/--
内部自己同型群
上の φ について、 Im(φ) ⊆ Aut G を内部自己同型群といい、 Inn Gと書く
-/
def Inn (G : Type) [Group G] : Set (Aut G) :=
  Im' φ

/-
準同型 :
`MonoidHom` というのがあるので、以降は `Hom` の代わりにこれを使います。
`Hom G H` を `MonoidHom G H` または `G →* H` とも書くことができます。

同型 :
`MulEquiv` というのがあるので、以降は `Iso` の代わりにこれを使います。
`Iso G H` を `MulEquiv` または `G ≃* H` とも書くことができます。

核 :
`MonoidHom.ker` というのがあるので、以降は `Ker` の代わりにこれを使います。
`Ker φ` を `φ.ker` と書くことができます。

像 :
`MonoidHom.range` というのがあるので、以降は `Im` の代わりにこれを使います。
`Im φ` を `φ.range` と書くことができます。
-/


/-! ## 同値関係、剰余類 -/

/-- 同値関係(equivalence relation) -/
structure Equivalence' {α : Type} (r : α → α → Prop) where
  refl : ∀ a, r a a -- 反射(reflexive)律
  symm : ∀ a b, r a b → r b a -- 対象(symmetric)律
  trans : ∀ a b c, r a b → r b c → r a c -- 推移(transitive)律

/-- 例: x = y という関係 -/
def x_eq_y {α : Type} [Group α] : α → α → Prop :=
  fun x y => x = y

/- 例: x = y を同値関係にしてみる -/
instance instEqEquiv' {α : Type} [Group α] : Equivalence' (@x_eq_y α _ ) where
  -- TODO: 証明を書く
  refl := sorry
  symm := sorry
  trans := sorry

/- `Equivalence` が定義されているので、以降は `Equivalence` を使います。 -/

/-
同値関係 - 同値類(equivalence class) - 商(quotient)について

条件を満たす関係 ⇒ 同値関係

同値類 : xと同値関係で同じになる値の集合
(例: 「2で割った余りが同じ」という同値関係の場合、2の同値類は{2, 4, 6, ...})

同値類の集合 ⇒ 商
(例: {1, 3, 5, ...}, {2, 4, 6, ...})

-/

/-- ライブラリーでは、同値関係を表すのに、 `Equivalence` というものを使う -/
instance instEqEquiv {α : Type} [Group α] : Equivalence (@x_eq_y α _) where
  refl := sorry
  symm := sorry
  trans := sorry

/-- ライブラリーでは、同値関係をもつ集合を `Setid` というものを使う -/
instance SetoidEq {α : Type} [Group α] : Setoid α where
  r := x_eq_y -- r : 同値関係
  iseqv := instEqEquiv -- 同値関係の証明

/-- ライブラリーでは、商集合を表すのに、 `Quotient` というものを使う
教科書では、同値関係 ~ による商集合は S/~ と書かれます。 -/
def QuotientEq {α : Type} [Group α] : Type := Quotient (SetoidEq : Setoid α)

/-- 同値関係による商集合の型、つまり同値類 -/
def QuotientBy {α : Type} (r : α → α → Prop) (h : Equivalence r) : Type :=
  Quotient { r := r, iseqv := ‹Equivalence r› }

/-
つまり、
同値関係 - 同値類 - 商が、それぞれライブラリーでどう表されているか
をまとめると、

同値関係: Equivalence
↓
同値関係を持つ集合: Setoid
↓
同値類: Quotient
-/

/-- S から S/~ への自然な写像(natural map) -/
def naturalMap {α : Type} (r : α → α → Prop) (h : Equivalence r) : α → Quotient (Setoid.mk r h) :=
  fun a => Quotient.mk (Setoid.mk r h) a


/-! ### 左剰余類(left coset) -/

/-- x⁻¹ * y ∈ H という関係 -/
def leftRel {G : Type} [Group G] (H : Subgroup G) (x y : G) : Prop :=
  x⁻¹ * y ∈ H

/-- x⁻¹ * y ∈ H は同値関係 -/
instance LeftRelEquiv {G : Type} [Group G] (H : Subgroup G) : Equivalence (leftRel H) :=
{
  refl := by
    intro h
    rw [leftRel]
    rw [inv_mul_cancel]
    apply one_mem
  ,
  -- TODO: 証明を書く
  symm := by
    intro h h2 h3
    rw [leftRel]
    rw [leftRel] at h3
    sorry
  ,
  -- TODO: 証明を書く
  trans := sorry
}

/-- 同値類を作るために、 x⁻¹ * y ∈ H の `Setoid` を作る -/
instance LeftRelSetoid {G : Type} [Group G] (H : Subgroup G) : Setoid G :=
{
    r := leftRel H,
    iseqv := LeftRelEquiv H
}

/-- 同値類 -/
def LeftCosetClass {G : Type} [Group G] (H : Subgroup G) (x : G) : Quotient (LeftRelSetoid H) :=
  Quotient.mk'' x

/-- 同値類 (`⟦⟧`を使った記法) -/
def LeftCosetClass' {G : Type} [Group G] (H : Subgroup G) (x : G) : Quotient (LeftRelSetoid H) :=
  ⟦x⟧

/-- この同値関係による商 つまり 左剰余類の集合
教科書では、 G/H と書かれます。 -/
def LeftCosetSet {G : Type} [Group G] (H : Subgroup G) : Type := Quotient (LeftRelSetoid H)


/-! ### 指数(index) -/

/-- 指数を定義するため、 G と H が有限の場合を定義 -/
instance FintypeLeftCosetSet {G : Type} [Group G] [Fintype G] (H : Subgroup G) [Fintype (↥H)] :
  Fintype (LeftCosetSet H) := sorry -- TODO: 証明を書く

/-- 指数: G/H の元の個数 -/
def index {G : Type} [Group G] [Fintype G] (H : Subgroup G) [Fintype (↥H)] : ℕ :=
  Fintype.card (LeftCosetSet H)


/-! ### 両側剰余類(double coset) -/

/-- 両側剰余類の関係 -/
def DoubleCosetRel {G : Type} [Group G] (H K : Subgroup G) (g₁ g₂ : G) : Prop :=
  ∃ h ∈ H, ∃ k ∈ K, g₁ = h * g₂ * k

/-- これは同値関係 -/
instance instDoubleCosetEquiv {G : Type} [Group G] (H K : Subgroup G) : Equivalence (DoubleCosetRel H K) :=
  sorry -- TODO: 証明を書く

/-- `Setoid` -/
instance instDoubleCosetSetoid {G : Type} [Group G] (H K : Subgroup G) : Setoid G :=
{
    r := DoubleCosetRel H K,
    iseqv := instDoubleCosetEquiv H K
}

/-- `Setoid` (`⟨⟩` を使った記法) -/
def instDoubleCosetSetoid' {G : Type} [Group G] (H K : Subgroup G) : Setoid G :=
  ⟨DoubleCosetRel H K, instDoubleCosetEquiv H K⟩

/-- 両側剰余類 -/
def DoubleCosetClass {G : Type} [Group G] (H K : Subgroup G) (x : G) :
    Quotient (instDoubleCosetSetoid H K) :=
  Quotient.mk (instDoubleCosetSetoid H K) x

/-- 同値関係による商、つまり両側剰余類の集合
教科書では、 H\G/K と書かれます -/
def doubleCoset {G : Type} [Group G] (H K : Subgroup G) :
    Type
  := Quotient (instDoubleCosetSetoid H K)


/-! ### 正規部分群 -/

/-- 正規部分群(normal subgroup)
教科書では、　G ▷ H と書かれます -/
def IsNormalSubgroup {G : Type} [Group G] (H : Subgroup G) : Prop :=
  ∀ g : G, ∀ h ∈ H, g * h * g ⁻¹ ∈ H

/- 正規部分群のクラス -/
class Normal {G : Type} [Group G] (H : Subgroup G) : Prop where
  conj_mem : IsNormalSubgroup H

/-- G/N の代表元の積 (gN)(hN) = (gh)N -/
def quotientMul {G : Type} [Group G] (H : Subgroup G) [Normal H] :
  Quotient (LeftRelSetoid H) → Quotient (LeftRelSetoid H) → Quotient (LeftRelSetoid H) :=
  -- Quotient.lift₂ は、 `Quotient` 上で変数が2個の関数を定義する関数(well-defined であることを助けてくれる)
  Quotient.lift₂
    (fun g h => Quotient.mk'' (g * h)) -- 定義する関数 (gN)(hN) = (gh)N
    (sorry) -- 関数が well-defined であることの証明 -- TODO: 証明を書く

-- 自前定義用に、KerをNormalのインスタンスにする(=Kerは正規部分群)
instance instKerNormal {G H : Type} [Group G] [Group H] (φ : Hom G H) :
    Normal (Ker φ.toFun) := sorry

/- `Subgroup.Normal` というのがあるので、以降はこれを使います。 -/

/-! ### 剰余群(factor group) -/

/-- 剰余群(商群(quotient group))の型 -/
def QuotientGroup {G : Type} [Group G] (N : Subgroup G) [Normal N] : Type :=
  Quotient (LeftRelSetoid N)

/-- 剰余群を群にする -/
instance instQuotientGroup {G : Type} [Group G] (N : Subgroup G) [Normal N] :
    Group (QuotientGroup N) :=
  {
    -- TODO: 証明を書く
    mul_assoc := sorry,
    mul := sorry,
    one := sorry,
    one_mul := sorry,
    mul_one := sorry,
    inv := sorry,
    inv_mul_cancel := sorry
  }

/-
商群(剰余群) :
`HasQuotient.Quotient` というのがあるので、以降は `QuotientGroup` の代わりにこれを使います。
`QuotientGroup G H` を `G ⧸ H` と書くことができます。
-/


/-! ### 準同型定理 -/

/-
準同型 φ : G → H に対して、
自然な準同型 π : G → G/Ker(φ)とするとき
φ = π ∘ ψ となるような
ψ : G/Ker(φ) → H がただひとつ存在し、
ψはG/Ker(φ)からIm(φ)への同型となる
-/

-- mathlibを使った定義
-- Mathlib.GroupTheory.QuotientGroup.Basic QuotientGroup.quotientKerEquivRange
/-- 準同型定理 -/
def firstIsomorphismTheorem {G H : Type} [Group G] [Group H] (φ : G →* H) :
    G ⧸ φ.ker ≃* φ.range := sorry

-- mathlibの定義を、自前定義版に置き換え
/-- 準同型定理 -/
def firstIsomorphismTheorem' {G H : Type} [Group G] [Group H] (φ : Hom G H) :
    Iso (QuotientGroup (Ker φ.toFun)) (Im φ.toFun) := sorry


/-- 準同型定理
教科書の定義に沿ったもの

φ : G → H を群の準同型、
π をG → G/Ker(φ) を自然な準同型とするとき、
φ = ψ ∘ π となるような準同型 ψ : G/Ker(φ) → H がただ一つ存在し、
ψ は G/Ker(φ) から Im(φ) への同型となる

QuotientGroup.mk' φ.ker は、自然な準同型を表す(上記の π に該当)
-/
theorem first_homomorphism_theorem {G H : Type} [Group G] [Group H] (φ : G →* H) :
    ∃! ψ : G ⧸ φ.ker →* H, ψ ∘ QuotientGroup.mk' φ.ker = φ
  := sorry

-- /-  -/
-- theorem a {G : Type} [Group G] {N : Subgroup G} [Subgroup.Normal N] :


theorem second_homomorphism_theorem {G : Type} [Group G] (H N : Subgroup G) [Subgroup.Normal N] :
    ∃ K : Subgroup G, K = H ⊔ N ∧ H ⊔ N = N ⊔ H ∧
    Subgroup.Normal (H ⊓ N) -- ∧ ...
    := sorry


/-! ### 群の作用(action) -/

/-- 群の作用
φ : G × X → X で、
- φ(1G, x) = x
- φ(g, φ(h, x)) = φ(g * x, x)
を満たすもの
g • x や gx とも書く

G の X への作用があるとき、「G は X に作用する」という。
-/
structure LeftAction {G X : Type} [Group G] (φ : G → X → X) : Prop where
  one_mul : ∀ x, φ 1 x = x
  mul_assoc : ∀ g h x, φ g (φ h x) = φ (g * h) x

/- 作用を表す `MulAction` があるので、以降はこちらを使います。
群 G が集合 X に作用することを `[MulAction G X]` と書くことができます。 -/

/- 軌道(orbit) -/
def orbit' {G X : Type} [Group G] [MulAction G X] (x : X) : Set X :=
  { y | ∃ g : G, g • x = y}

/- `MulAction.orbit` というのがあるので、以降はこちらを使います。 -/


/- 安定化群(stabilizer) -/
def stabilizer' {G X : Type} [Group G] [MulAction G X] (x : X) : Set G :=
  { g | ∃ g : G, g • x = x}

/- `stabilizer` というのがあるので、以降はこちらを使います。 -/

/- 共役類 -/

/- 交換子(commutator) -/
def commutator' {G : Type} [Group G] (a b : G) : G :=
  a * b * a⁻¹ * b⁻¹

/-- { [a, b] | a ∈ H, b ∈ K } で構成される G の部分群 -/
def commutatorSubgroup {G : Type} [Group G] (H : Subgroup G) (K : Subgroup G) : Subgroup G :=
  {
    carrier := { g | ∃ a ∈ H, ∃ b ∈ K, g = commutator' a b },
    mul_mem' := sorry,
    one_mem' := sorry,
    inv_mem' := sorry
  }

/-- 交換子群 -/
def commutatorGroup {G : Type} [Group G] : Subgroup G :=
  commutatorSubgroup (⊤ : Subgroup G) (⊤ : Subgroup G)

/-
交換子群は
`commutator` というのがあるので、こちらを使います。
`commutator G` 、または `⁅_, _⁆` と書きます。
-/

