namespace HW_IV_3
universe u
variable {α : Sort u} {β : Type u}


def Refl (R : α → α → Prop) := ∀ x, R x x

def Symm (R : α → α → Prop) := ∀ x y, R x y → R y x

def AntiSymm (R : α → α → Prop) := ∀ x y, R x y → R y x → x = y

def Trans (R : α → α → Prop) := ∀ x y z, R x y → R y z → R x z

inductive ReflC (R : α → α → Prop) : α → α → Prop where
  | base {x y} : R x y → ReflC R x y
  | refl {x} : ReflC R x x

inductive SymmC (R : α → α → Prop) : α → α → Prop where
  | base {x y} : R x y → SymmC R x y
  | symm {x y} : R x y → SymmC R y x

inductive TransC (R : α → α → Prop) : α → α → Prop where
  | base {x y} : R x y → TransC R x y
  | trans {x y z} : R x y → TransC R y z → TransC R x z


-- 1 ---------------------
-- They were all completed

-- 2 ---------------------
-- They were all completed

-- 3 ---------------------
-- They were all completed

-- 4 ---------------------
example (R : α → α → Prop)
  : Symm R → ∀ x y, R x y ↔ (SymmC R) x y := by
    intro h x y
    constructor
    intro h1
    exact SymmC.base (h y x (h x y h1))
    intro h1
    cases h1 with
    | base a => exact a
    | symm a => exact h y x a


-- 5 ---------------------
example (R : α → α → Prop) : ∀ x y,
  ReflC (TransC R) x y ↔ TransC (ReflC R) x y := by
  intro x y
  constructor
  intro h
  

end HW_IV_3
