import Mathlib

set_option linter.style.longLine false

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

namespace HW_III_4

inductive Person where | mary | steve | ed | jolin

open Person

def on_right (p q : Person) : Prop := match p with
  | mary => q = steve
  | steve => q = ed
  | ed => q = jolin
  | jolin => q = mary

-- 1

def on_left (p q : Person) : Prop := on_right q p


-- 2
example : on_left mary jolin := rfl


-- 3
variable (α : Type) (P Q : α → Prop)
example : (∀ x, P x → Q x) → (∀ x, P x) → (∀ x, Q x) :=
  fun a b c => (a c) (b c)

-- 4
example : ∃ x, on_right mary x := ⟨steve, rfl⟩
example : ∃ x, ¬on_right mary x := ⟨mary, Person.noConfusion⟩

-- 5
example : ∀ x , ∃ y, y = neg x := fun a => Exists.intro a.neg rfl

-- 6
example : (∀ x, P x → r) ↔ (∃ x, P x) → r := ⟨fun a b => Exists.elim b a, fun a b c => a (Exists.intro b c)⟩
example : (∃ x, P x ∨ Q x) ↔ (∃ x, P x) ∨ (∃ x, Q x) := ⟨fun a => Exists.elim a (fun b c => Or.elim c (fun d => Or.intro_left (∃ x, Q x) (Exists.intro b d)) (fun e => Or.elim c (fun _ => Or.intro_right (∃ x, P x) (Exists.intro b e)) (fun _ => Or.intro_right (∃ x, P x) (Exists.intro b e)))), fun a => Or.elim a (fun b => Exists.elim b (fun c d => Exists.intro c (Or.intro_left (Q c) d))) (fun b => Exists.elim b (fun c d => Exists.intro c (Or.intro_right (P c) d)))⟩

-- 7
def next_to (a : Person) (b : Person) := on_left a b ∨ on_left b a


example : ∀ p q , on_right p q → next_to p q := fun a b c => Or.intro_right (on_left a b) c
example : ∀ p : Person, ∃ q : Person, next_to p q := fun a => match a with
  | mary => Exists.intro steve (Or.intro_right (on_left mary steve) rfl)
  | steve => Exists.intro ed (Or.intro_right (on_left steve ed) rfl)
  | ed => Exists.intro jolin (Or.intro_right (on_left ed jolin) rfl)
  | jolin => Exists.intro mary (Or.intro_right (on_left jolin mary) rfl)

example : ∀ p : Person, ∃ q : Person, ¬next_to p q := fun a => match a with
  | mary => Exists.intro ed (fun b => Or.elim b (fun c => nomatch c) (fun c => nomatch c))
  | steve => Exists.intro jolin (fun b => Or.elim b (fun c => nomatch c) (fun c => nomatch c))
  | ed => Exists.intro mary (fun b => Or.elim b (fun c => nomatch c) (fun c => nomatch c))
  | jolin => Exists.intro jolin (fun b => Or.elim b (fun c => nomatch c) (fun c => nomatch c))


-- 8
inductive Exists1 {α : Type} (p : α → Prop) : Prop where
  | intro (x : α) (h : p x ∧ ∀ y : α, p y → x = y) : Exists1 p

theorem Exists1.elim {α : Type} {P : α → Prop} {b : Prop}
   (h₁ : Exists1 (fun x => P x)) (h₂ : ∀ (a : α), P a → b) : b := match h₁ with | intro c d => h₂ c d.left

-- 9
example : ∀ x, Exists1 (fun y : Person => x ≠ y ∧ ¬next_to y x ) := fun a => match a with
  | mary => Exists1.intro ed ⟨⟨(fun b => nomatch b), (fun c => nomatch c)⟩, fun b c => match b with
    | mary => nomatch c.left
    | steve => nomatch (c.right (Or.intro_left (on_left mary steve) rfl))
    | ed => rfl
    | jolin => nomatch (c.right (Or.intro_right (on_left jolin mary) rfl))
    ⟩
  | steve => Exists1.intro jolin ⟨⟨(fun b => nomatch b), (fun c => nomatch c)⟩, fun b c => match b with
    | steve => nomatch c.left
    | mary => nomatch (c.right (Or.intro_right (on_left mary steve) rfl))
    | jolin => rfl
    | ed => nomatch (c.right (Or.intro_left (on_left steve ed) rfl))
    ⟩
  | ed => Exists1.intro mary ⟨⟨(fun b => nomatch b), (fun c => nomatch c)⟩, fun b c => match b with
    | ed => nomatch c.left
    | steve => nomatch (c.right (Or.intro_right (on_left steve ed) rfl))
    | mary => rfl
    | jolin => nomatch (c.right (Or.intro_left (on_left ed jolin) rfl))
    ⟩
  | jolin => Exists1.intro steve ⟨⟨(fun b => nomatch b), (fun c => nomatch c)⟩, fun b c => match b with
    | jolin => nomatch c.left
    | mary => nomatch (c.right (Or.intro_left (on_left jolin mary) rfl))
    | steve => rfl
    | ed => nomatch (c.right (Or.intro_right (on_left ed jolin) rfl))
    ⟩

example : Exists1 ( fun x => P x ) → ¬ ∀ x, ¬ P x := fun a b => match a with | ⟨c, d⟩ => (b c) d.left
example : Exists1 (fun x => x=0) := ⟨0, ⟨rfl, fun _ a => a.symm⟩⟩
example : ¬Exists1 (fun x => x ≠ 0) := fun a => match a with | ⟨b, c⟩ => nomatch (Eq.trans (((c.right 1) (fun d => nomatch d)).symm : 1 = b) (((c.right 2) (fun d => nomatch d)) : b = 2))




end HW_III_4
