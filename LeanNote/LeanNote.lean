import Mathlib.Data.Set.Notation
import Mathlib.Data.Nat.Notation
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.Subgroup.Defs

/-!
本リポジトリーのleanファイルを読む時、
正確ではありませんが、**だいたい**このようにとらえて読めば
割と近い理解ができるのではないでしょうか、という説明です。
-/


/- ## `def`

`def ...`
何かを定義する
-/
def two : ℕ := 1 + 1

/-
def {定義するものの名前} : {定義するものの型} := {定義の内容}
-/


/- ## `sorry`

`:= sorry`
定義の内容を省略する
 -/
def three : ℕ := sorry


/- ## `(...)`, `{...}`

`{X : Type}`
集合Xがあるとき

`(x : X)`
x ∈ X
-/
def f {X : Type} {Y : Type} (x : X) (y : Y) : Y := sorry
-- 集合 X 、集合 Y がある時、 x ∈ X 、 y ∈ Y について…


/- ## `structure`

`structure ...`
性質を持った構造を定義

structure {名前} where
  {性質の名前} : {性質の型}
  {性質の名前} : {性質の型}
  ...
-/
structure Perm (α : Type) where
  f : α → α
  g : α → α


/- ## `class`

`class ...`
性質を持った構造を定義

class {名前} where
  {性質の名前} : {性質の型}
  {性質の名前} : {性質の型}

structure と違って、
`[{class の名前} ...]`
と書くことで、 `...` に class の性質を付加できる
-/

class Group' (α : Type) where
  mul : α → α → α
  one : α

def setOne {G : Type} [Group' G] : Set G :=
  { x | Group'.one = x }
-- G は Group' の性質がある


/- ## `instance`

何かが class 、 structure の性質を持つことを示す

```
instance {インスタンスの名前}(省略可) : {class または structure の名前} {性質を持たせるもの} where
  {性質} := {性質の証明}
  {性質} := {性質の証明}
  ...
```
-/
instance instSetoid {G : Type} [Group G] (H : Subgroup G) : Setoid G where
  r := sorry
  iseqv := sorry


/- ## `Prop`

... {名前} : Prop := ...
{名前} が命題であることを表す
-/

/- x が 1 と等しいか？という命題 -/
def eqOne (x : ℕ) : Prop := x = 1


/- ## `... → ...`
... から ... への写像

`X → Y`
集合 X から 集合 Y への写像
-/
def g {X : Type} {Y : Type} : X → Y := sorry


/- ## 集合

`{ x | P x }`
条件 P を満たす x の集合
-/
def even  : Set ℕ :=
  { n | n % 2 = 0 }


/- ## `∀ x, ...`

すべての x について、...が成り立つ
-/
def forallX : ∀ x, x + x = 2 * x := sorry


/- ## `∃ y, ...`
...が成り立つ y が少なくとも1つ存在する
-/
def existY : ∃ y, y + 0 = 1 := sorry
