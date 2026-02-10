import mathlib

namespace HW_III_6

universe u

inductive MyEq {α : Sort u} : α → α → Prop where
  | refl a : MyEq a a

#check MyEq 1 2

example : MyEq 1 1 :=
  MyEq.refl 1

infix:50 " ~ "  => MyEq

#check 1 ~ 1

theorem MyEq.subst {α : Sort u} {P : α → Prop} {a b : α}
                   (h₁ : a ~ b) (h₂ : P a) : P b := by
  cases h₁ with
  | refl => exact h₂

example {x y : Nat} : x ~ y → (x > 2 ↔ y > 2) := by
  intro h
  apply MyEq.subst h       -- goal becomes x > 2 ↔ x > 2
  exact ⟨ id, id ⟩

theorem MyEq.sym {α : Sort u} {a b : α} : a ~ b → b ~ a := by
  intro h
  apply MyEq.subst h
  exact MyEq.refl a

theorem MyEq.trans {α : Sort u} {a b c : α} : a ~ b → b ~ c → a ~ c := by
  intro hab hbc
  exact MyEq.subst hbc hab

theorem MyEq.congr_arg {α : Sort u} {a b : α} {f : α → α} : a ~ b → f a ~ f b := by
  intro hab
  apply MyEq.subst hab
  exact MyEq.refl (f a)

example (x y : Nat) : x ~ y → 2*x+1 ~ 2*y + 1 :=
  fun h => MyEq.congr_arg (f := fun w => 2*w + 1) h

-- example (x y : Nat) : x ~ y → 2*x+1 ~ 2*y + 1 := -- fails
--   fun h => MyEq.congr_arg h

example (x y : Nat) : x ~ y → 2*x ~ 2*y :=
  fun h => MyEq.congr_arg h


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








-- 1
theorem MyEq.to_iff (a b : Prop) : a ~ b → (a ↔ b) := by
  intro h
  cases h with
  | refl => exact ⟨id, id⟩

-- 2
example (P : Type → Prop) : ∀ x y, x = y → P x → ∃ z, P z := by
  intro α₁ α₂ h₃ h₄
  use α₁
  <;> sorry


inductive Spin where | up | dn
open Spin

def Spin.toggle : Spin → Spin
  | up => dn
  | dn => up

postfix : 95 " ⁻¹ " => toggle

@[simp] theorem toggle_up : up⁻¹ = dn := rfl
@[simp] theorem toggle_dn : dn⁻¹ = up := rfl
@[simp] theorem toggle_toggle : x⁻¹⁻¹ = x := by cases x <;> simp

def op (x y : Spin) : Spin := match x, y with
  | up, dn => dn
  | dn, up => dn
  | _, _ => up

infix:75 " o " => op

@[simp] theorem op_up_left {x}  : up o x = x := by cases x <;> rfl
@[simp] theorem op_up_right {x} : x o up = x := by cases x <;> rfl
@[simp] theorem op_dn_left {x}  : dn o x = x⁻¹ := by cases x <;> rfl
@[simp] theorem op_dn_right {x} : x o dn = x⁻¹ := by cases x <;> rfl

@[simp] theorem toggle_op_left {x y} : (x o y)⁻¹ = x⁻¹ o y := by
  cases x <;> simp


-- 3
theorem assoc {x y z} : x o (y o z) = (x o y) o z := by cases x <;> simp

theorem com {x y} : x o y = y o x := by cases x <;> simp

theorem toggle_op_right {x y} : (x o y)⁻¹ = y o x⁻¹ := by cases x <;> simp

@[simp]
theorem inv_cancel_right {x} : x o x⁻¹ = dn := by cases x <;> simp

@[simp]
theorem inv_cancel_left {x} : x⁻¹ o x = dn := by cases x <;> simp



-- 4
def T (n : Nat) : Nat := match n with
  | Nat.zero => 0
  | Nat.succ x => n*n + T x

example (n : Nat) : 6 * (T n) = n * (n+1) * (2*n+1) := by
  induction n with
  | zero =>
    simp
    rfl
  | succ k ih =>
    unfold T  -- interesting that this is required
    nlinarith


-- 5
example (x : PreDyadic) : zero ≠ add_one x := PreDyadic.noConfusion

example : ¬zero.add_one = zero.add_one.add_one.half := PreDyadic.noConfusion

-- 6
example (x y : PreDyadic) : add_one x = add_one y ↔ x = y := ⟨sorry, sorry⟩





-- 7
end HW_III_6
