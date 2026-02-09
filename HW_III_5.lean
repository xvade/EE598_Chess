import Mathlib

inductive Person where | mary | steve | ed | jolin

open Person

def on_right (p q : Person) : Prop := match p with
  | mary => q = steve
  | steve => q = ed
  | ed => q = jolin
  | jolin => q = mary

def on_left (p q : Person) : Prop := on_right q p

def next_to (a : Person) (b : Person) := on_left a b ∨ on_left b a


inductive PreDyadic where
  | zero    : PreDyadic
  | add_one : PreDyadic → PreDyadic  -- x ↦ x + 1
  | half    : PreDyadic → PreDyadic  -- x ↦ x / 2
  | neg     : PreDyadic → PreDyadic  -- x ↦ -x

def Double : PreDyadic → PreDyadic
  | .zero      => .zero
  | .add_one a => .add_one (.add_one (Double a))
  | .half a    => a
  | .neg a     => .neg (Double a)

-- def depth : PreDyadic → ℕ
--   | .zero => 0
--   | .add_one a => 1 + depth a
--   | .half a => 2 + depth a
--   | .neg a => 1 + depth a


def add (a : PreDyadic) (b : PreDyadic) :=
match a, b with
| .zero, y => y
| .add_one x, y => .add_one (add x y)
| .half x, y => .half (add x (Double y))
| .neg x, y => .neg (add x (.neg y))

def mul (a : PreDyadic) (b : PreDyadic) :=
  match a, b with
  | .zero, _ => PreDyadic.zero
  | .add_one x, y => add y (mul x y)
  | .half x, y => .half (mul x y)
  | .neg x, y => .neg (mul x y)

def to_rat (a : PreDyadic) : ℚ :=
  match a with
  | .zero => 0 / 1
  | .add_one x => (to_rat x) + 1
  | .half x => (to_rat x) / 2
  | .neg x => - (to_rat x)


open PreDyadic

namespace HW_III_5

-- 1
variable (P Q : Type → Prop)


example : (¬ ∃ x, P x) ↔ (∀ x, ¬ P x) := by
  apply Iff.intro
  · intro h x hp
    exact h (Exists.intro x hp)
  · intro h hepx
    apply Exists.elim hepx
    intro x hpa
    exact (h x) hpa


example : (∃ x, P x ∧ Q x) →  ∃ x, Q x ∧ P x := by
  intro h
  apply Exists.elim h
  intro α h1
  use α
  apply And.intro
  · exact h1.right
  exact h1.left

example : (∃ x, P x ∨ Q x) →  ∃ x, Q x ∨ P x := by
  intro h
  apply Exists.elim h
  intro a h1
  use a
  cases h1 with
  | inl h2 => exact Or.inr h2
  | inr h2 => exact Or.inl h2


-- 2
example : ∀ p : Person, ∃ q : Person, next_to p q := by
  intro a
  cases a
  · use steve
    apply Or.intro_right
    rfl
  · use ed
    apply Or.intro_right
    rfl
  · use jolin
    apply Or.intro_right
    rfl
  · use mary
    apply Or.intro_right
    rfl


example : ∀ p : Person, ∃ q : Person, ¬next_to p q := by
  intro a
  cases a
  · use ed
    intro h
    apply Or.elim h
    · intro h1
      nomatch h1
    intro h1
    nomatch h1
  · use jolin
    intro h
    apply Or.elim h
    · intro h1
      nomatch h1
    intro h1
    nomatch h1
  · use mary
    intro h
    apply Or.elim h
    · intro h1
      nomatch h1
    intro h1
    nomatch h1
  · use steve
    intro h
    apply Or.elim h
    · intro h1
      nomatch h1
    intro h1
    nomatch h1

-- 3a
def no_negs (x : PreDyadic) : Prop := match x with
| zero => True
| add_one a => no_negs a
| half a => no_negs a
| neg _ => False

-- 3b
example (x : PreDyadic) : no_negs x → no_negs (Double x) := by
  intro h1
  cases x


-- 3c



end HW_III_5
