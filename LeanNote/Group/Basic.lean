import LeanNote.Group.Defs

/!-  -/

-- φ : G → Aut G を φ g = ig と定義する。
def φ {G : Type} [Group G] : G → Aut G :=
  fun g => {
    toFun := ig g,
    autoIso := innerAutoIso g
  }

-- この時、φは準同型である
-- φ は、 (φ : G → Aut G) にしないとエラー(typeclass instance problem is stuck, it is often due to metavariables)になった
def phi_hom {G : Type} [Group G] : Hom (φ : G → Aut G) :=
  {
    hom := sorry
  }
