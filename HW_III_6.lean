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
  use α₂
  exact h₃ ▸ h₄




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
    linarith




-- 5
example (x : PreDyadic) : zero ≠ add_one x := PreDyadic.noConfusion

example : ¬zero.add_one = zero.add_one.add_one.half := PreDyadic.noConfusion

-- 6
example (x y : PreDyadic) : add_one x = add_one y ↔ x = y := ⟨
  by
    intro h
    exact congrArg
      (fun a => match a with
        | zero => zero
        | add_one b => b
        | half b => b
        | neg b => b) h,
  congrArg add_one
⟩



structure Point (α : Type u) where
  x : α
  y : α

theorem Point.ext {α : Type} (p q : Point α) (hx : p.x = q.x) (hy : p.y = q.y)
  : p = q := by
  cases p with | mk a b =>
  cases q with | mk c d =>
  simp_all

example (x y : Nat) : Point.mk (x+y) (x+y) = Point.mk (y+x) (y+x) := by
  apply Point.ext
  · exact add_comm x y
  · exact add_comm x y

@[ext]
structure Komplex where
  re : ℝ
  im : ℝ

example (x y : ℝ) : Komplex.mk (x+y) (x+y) = Komplex.mk (y+x) (y+x) := by
  ext
  · exact add_comm x y
  · exact add_comm x y


def shift (k x : ℤ) : ℤ := x+k

@[simp]
theorem shift_inv_right {k} : shift k ∘ shift (-k) = id := by
  funext x              -- x : ℤ ⊢ (shift k ∘ shift (-k)) x = id x
  simp[shift]

@[simp]
theorem shift_inv_left {k} : shift (-k) ∘ shift k = id := by
  funext x
  simp[shift]

open Function

example {k} : Bijective (shift k) := by
  rw[bijective_iff_has_inverse]
  use shift (-k)
  constructor
  · simp[leftInverse_iff_comp]     -- uses shift_inv_left
  · simp[rightInverse_iff_comp]    -- uses shift_inv_right

-- 7 ------------------
@[simp] theorem shift_zero : shift 0 = id := by
  funext x
  unfold shift
  simp

@[simp] theorem shift_add {j k} : shift k ∘ shift j = shift (j+k) := by
  unfold shift
  simp



-- 8 -----------------
example : Double ∘ half = id := by
  funext x
  simp
  rfl

-- 9  -------------------
def spin_bool_equiv : Spin ≃ Bool := {
  toFun := fun a => match a with | up => true | dn => false,
  invFun := fun a => match a with | true => up | false => dn,
  left_inv := by
    intro x
    cases x with
    | up => rfl
    | dn => rfl
  right_inv := by
    intro x
    cases x with
    | true => rfl
    | false => rfl
}

-- 10 This took me 9 hours (I counted) (and that's a good thing—I know more Lean now)
@[ext]
structure K1 where
  re : ℝ
  im : ℝ

@[ext]
structure K2 where
  a : ℝ
  θ : ℝ
  pa : 0 ≤ a
  pθ : -Real.pi ≤ θ ∧ θ < Real.pi
  h : a = 0 → θ = 0

noncomputable def make_K2_from_K1 (k1 : K1) : K2 :=
  let a := (√(k1.re ^ 2 + k1.im ^ 2))
  let θ := (
    if k1.re = 0 then (
      if k1.im = 0 then 0 else
        if k1.im > 0 then Real.pi/2 else -(Real.pi/2)
    ) else (
      if k1.re > 0 then Real.arctan (k1.im / k1.re) else (
        if Real.arctan (k1.im / k1.re) < 0 then Real.pi + Real.arctan (k1.im / k1.re) else -Real.pi + Real.arctan (k1.im / k1.re)
        )
      )
  )
  have pa : 0 ≤ a := by positivity
  have pθ : -Real.pi ≤ θ ∧ θ < Real.pi := ⟨
    (by
      unfold θ
      split_ifs with h1 h2 h3 h4 h5
      · simp only [Left.neg_nonpos_iff]
        exact Real.pi_nonneg
      · have h : Real.pi / 2 > 0 := by
          exact Real.pi_div_two_pos
        have h' : -Real.pi < 0 := neg_neg_iff_pos.mpr Real.pi_pos
        have h'' : -Real.pi < Real.pi / 2 := by exact Std.lt_trans h' h
        exact Std.le_of_lt h''
      · have h (a : Real) (h : a > 0): a / 2 < a := by aesop
        have h' := h Real.pi Real.pi_pos
        have h'': -(Real.pi / 2) > -Real.pi := by aesop
        exact Std.le_of_lt h''
      · have h (a : ℝ) : -(Real.pi / 2) < Real.arctan a := by
          exact Real.neg_pi_div_two_lt_arctan a
        have h' (a : Real) (h : a > 0): a / 2 < a := by aesop
        have h'' := h' Real.pi Real.pi_pos
        have h''': -(Real.pi / 2) > -Real.pi := by aesop
        grind
      · have h : -Real.pi ≤ Real.arctan (k1.im / k1.re) := by
          have h (a : ℝ) : -(Real.pi / 2) < Real.arctan a := by
            exact Real.neg_pi_div_two_lt_arctan a
          have h' (a : Real) (h : a > 0): a / 2 < a := by aesop
          have h'' := h' Real.pi Real.pi_pos
          have h''': -(Real.pi / 2) > -Real.pi := by aesop
          grind
        grind
      · suffices 0 ≤ Real.arctan (k1.im / k1.re) by
          exact (le_add_iff_nonneg_right (-Real.pi)).mpr this
        grind
    ),
    (by
      unfold θ
      split_ifs with h1 h2 h3 h4 h5
      · exact Real.pi_pos
      · have h' (a : Real) (h : a > 0): a / 2 < a := by aesop
        exact h' Real.pi Real.pi_pos
      · have h : Real.pi > 0 := by
          exact Real.pi_pos
        have h' : -(Real.pi / 2) < 0 := neg_neg_iff_pos.mpr Real.pi_div_two_pos
        have h'' : -(Real.pi / 2) < Real.pi := by exact Std.lt_trans h' h
        exact Std.lt_trans h' h
      · have h : Real.arctan (k1.im / k1.re) < Real.pi := by
          have h (a : ℝ) : Real.arctan a < Real.pi / 2 := by
            exact Real.arctan_lt_pi_div_two a
          have h' (a : Real) (h : a > 0): a / 2 < a := by aesop
          have h'' := h' Real.pi Real.pi_pos
          have h''': -(Real.pi / 2) > -Real.pi := by aesop
          grind
        grind
      · suffices Real.arctan (k1.im / k1.re) < 0 by
          exact add_lt_iff_neg_left.mpr h5
        grind
      · suffices Real.arctan (k1.im / k1.re) < Real.pi by
          exact add_lt_of_neg_of_lt (neg_neg_iff_pos.mpr Real.pi_pos) this
        have h := Real.pi_pos
        have h' := Real.arctan_lt_pi_div_two (k1.im / k1.re)
        have h'' : Real.pi / 2 < Real.pi := by exact div_two_lt_of_pos h
        exact Std.lt_trans h' h''
    )
  ⟩
  K2.mk
    a
    θ
    pa
    pθ
    (by
      unfold a θ
      by_cases (k1.re = 0)
      · expose_names
        intro h1
        simp [h]
        intro h2
        absurd h1
        simp[*]
        positivity
      · expose_names
        intro h1
        simp only [gt_iff_lt]
        absurd h1
        positivity
    )

noncomputable def K_equiv : K1 ≃ K2 := {
  toFun := make_K2_from_K1,
  invFun := fun k2 => K1.mk
    (k2.a * Real.cos k2.θ)
    (k2.a * Real.sin k2.θ),
  left_inv := (
    by
      intro x
      simp
      by_cases (x.re = 0)
      · expose_names
        unfold make_K2_from_K1
        simp_all
        by_cases (x.im = 0)
        · simp_all
          expose_names
          exact K1.ext (Eq.symm h) (Eq.symm h_1)
        · expose_names
          simp_all
          by_cases (0 < x.im)
          · expose_names
            simp_all
            have h2 : x.im = √(x.im ^ 2) := by
              rw [Real.sqrt_sq_eq_abs]
              exact Eq.symm (abs_of_pos h_2)
            rw[← h, ← h2]
          · expose_names
            simp_all
            by_cases (0 < x.im)
            · expose_names
              simp_all
              absurd h_2
              exact not_le_of_gt h_3
            · expose_names
              simp_all
              have h_3 : x.im < 0 := Std.lt_of_le_of_ne h_2 h_1
              have h' : ¬ (0 < x.im) := not_lt_of_ge h_2
              simp[h']
              have h_4 : x.im = -√(x.im ^ 2) := by
                rw [Real.sqrt_sq_eq_abs, abs_of_neg]
                simp
                exact h_3
              rw[← h_4, ← h]
      · expose_names
        unfold make_K2_from_K1
        simp_all
        by_cases (x.re > 0)
        ·
          simp_all
          rw[Real.cos_arctan]
          have h1 : ((1 : ℝ) / √(1 + (x.im / x.re) ^ 2) = x.re / √(x.im^2 + x.re^2)) := by
            rw[div_pow x.im x.re 2]
            have h1 : 1 = (x.re ^ 2) / (x.re ^ 2) := by
              aesop
            rw[h1, (add_div (x.re ^ 2) (x.im ^ 2) (x.re ^ 2)).symm, ← h1, Real.sqrt_div, Real.sqrt_sq]
            simp
            rw[add_comm]
            positivity
            positivity
          rw[h1, add_comm]
          have h2 : √(x.im ^ 2 + x.re ^ 2) ≠ 0 := by positivity
          have h3 : √(x.im ^ 2 + x.re ^ 2) * (x.re / √(x.im ^ 2 + x.re ^ 2)) = x.re := by
            exact mul_div_cancel₀ x.re h2
          rw[h3, Real.sin_arctan]
          -- clear * - h
          rw [div_eq_mul_one_div (x.im / x.re) √(1 + (x.im / x.re) ^ 2), h1]
          have h4 : √(x.im ^ 2 + x.re ^ 2) * (x.im / x.re * (x.re / √(x.im ^ 2 + x.re ^ 2))) = x.im := by
            grind
          rw[h4]
        ·
          by_cases (Real.arctan (x.im / x.re) < 0)
          ·
            simp[*]
            have h''' (a : Real) : Real.cos (Real.pi + a) = -Real.cos a := by
              rw[add_comm]
              simp
            split_ifs with h1
            ·
              rw[h''', Real.cos_arctan]
              have h1 : ((1 : ℝ) / √(1 + (x.im / x.re) ^ 2) = -x.re / √(x.im^2 + x.re^2)) := by
                rw[div_pow x.im x.re 2]
                have h1 : 1 = (x.re ^ 2) / (x.re ^ 2) := by
                  aesop
                rw[h1, (add_div (x.re ^ 2) (x.im ^ 2) (x.re ^ 2)).symm, ← h1, Real.sqrt_div, Real.sqrt_sq_eq_abs, abs_of_neg]
                simp
                rw[add_comm]
                grind
                positivity
              rw[h1, add_comm]
              have h2 : √(x.im ^ 2 + x.re ^ 2) ≠ 0 := by positivity
              have h3 : √(x.im ^ 2 + x.re ^ 2) * (x.re / √(x.im ^ 2 + x.re ^ 2)) = x.re := by
                exact mul_div_cancel₀ x.re h2
              have h4 (a b : Real) : -(-a/b) = a/b := by
                grind
              rw[h4, h3, add_comm Real.pi]
              simp
              rw[Real.sin_arctan]
              -- clear * - h
              rw [div_eq_mul_one_div (x.im / x.re) √(1 + (x.im / x.re) ^ 2), h1]
              have h4 : √(x.im ^ 2 + x.re ^ 2) * (x.im / x.re * (x.re / √(x.im ^ 2 + x.re ^ 2))) = x.im := by
                grind
              have h5 : -(√(x.im ^ 2 + x.re ^ 2) * (x.im / x.re * (-x.re / √(x.im ^ 2 + x.re ^ 2)))) = (√(x.im ^ 2 + x.re ^ 2) * (x.im / x.re * (x.re / √(x.im ^ 2 + x.re ^ 2)))) := by
                grind
              rw[h5, h4]
            ·
              have h''' (a : Real) : Real.cos (-Real.pi + a) = -Real.cos a := by
               aesop
              rw[h''', Real.cos_arctan]
              have h1 : ((1 : ℝ) / √(1 + (x.im / x.re) ^ 2) = -x.re / √(x.im^2 + x.re^2)) := by
                rw[div_pow x.im x.re 2]
                have h1 : 1 = (x.re ^ 2) / (x.re ^ 2) := by
                  aesop
                rw[h1, (add_div (x.re ^ 2) (x.im ^ 2) (x.re ^ 2)).symm, ← h1, Real.sqrt_div, Real.sqrt_sq_eq_abs, abs_of_neg]
                simp
                rw[add_comm]
                grind
                positivity
              rw[h1, add_comm]
              have h2 : √(x.im ^ 2 + x.re ^ 2) ≠ 0 := by positivity
              have h3 : √(x.im ^ 2 + x.re ^ 2) * (x.re / √(x.im ^ 2 + x.re ^ 2)) = x.re := by
                exact mul_div_cancel₀ x.re h2
              have h4 (a b : Real) : -(-a/b) = a/b := by
                grind
              rw[h4, h3]
              have h5 (a : ℝ) : -Real.sin a = Real.sin (-Real.pi + a) := by aesop
              rw[← h5]
              rw[Real.sin_arctan]
              -- clear * - h
              rw [div_eq_mul_one_div (x.im / x.re) √(1 + (x.im / x.re) ^ 2), h1]
              have h4 : √(x.im ^ 2 + x.re ^ 2) * -(x.im / x.re * (-x.re / √(x.im ^ 2 + x.re ^ 2))) = x.im := by
                grind
              rw[h4]
          ·
            split_ifs with h1 h2
            ·
              have him : √(x.re ^ 2 + x.im ^ 2) * (x.im / x.re / √(1 + (x.im / x.re) ^ 2)) = x.im := by grind
              have hre : √(x.re ^ 2 + x.im ^ 2) * (1 / √(1 + (x.im / x.re) ^ 2)) = x.re := by grind
              rw[Real.sin_arctan, Real.cos_arctan, hre, him]
            · aesop
            ·
              have h3 :  Real.cos (-Real.pi + Real.arctan (x.im / x.re)) =  -Real.cos (Real.arctan (x.im / x.re)) := by
                rw[add_comm, ←sub_eq_add_neg]
                exact Real.cos_sub_pi (Real.arctan (x.im / x.re))
              rw[h3]
              have h3' :  Real.sin (-Real.pi + Real.arctan (x.im / x.re)) =  -Real.sin (Real.arctan (x.im / x.re)) := by
                rw[add_comm, ←sub_eq_add_neg]
                exact Real.sin_sub_pi (Real.arctan (x.im / x.re))
              rw[h3']
              rw[Real.cos_arctan, Real.sin_arctan]
              have h4 : ((1 : ℝ) / √(1 + (x.im / x.re) ^ 2) = -x.re / √(x.im^2 + x.re^2)) := by
                  rw[div_pow x.im x.re 2]
                  have h1 : 1 = (x.re ^ 2) / (x.re ^ 2) := by
                    aesop
                  rw[h1, (add_div (x.re ^ 2) (x.im ^ 2) (x.re ^ 2)).symm, ← h1, Real.sqrt_div, Real.sqrt_sq_eq_abs]
                  grind
                  positivity
              have h'' : √(x.im ^ 2 + x.re ^ 2) ≠ 0 := by positivity
              have hre : √(x.re ^ 2 + x.im ^ 2) * -(1 / √(1 + (x.im / x.re) ^ 2)) = x.re := by
                rw[h4]
                simp
                have h' (a b: ℝ) : -a / b = -(a / b) := by exact neg_div b a
                rw[h']
                simp
                rw[add_comm]
                grind
              rw[hre]
              have him : √(x.re ^ 2 + x.im ^ 2) * -(x.im / x.re / √(1 + (x.im / x.re) ^ 2)) = x.im := by
                have h''' : (x.im / x.re / √(1 + (x.im / x.re) ^ 2)) = (x.im / x.re) * (1 / √(1 + (x.im / x.re) ^ 2)) := by grind
                rw[h''']
                rw[h4, add_comm]
                grind
              rw[him]
  ),
  right_inv := (
    by
      intro x
      unfold make_K2_from_K1
      simp
      have ha : √((x.a * Real.cos x.θ) ^ 2 + (x.a * Real.sin x.θ) ^ 2) = x.a := by
        rw[mul_pow, mul_pow, add_comm, ← mul_add, Real.sin_sq_add_cos_sq]
        simp
        rw[Real.sqrt_sq_eq_abs]
        exact abs_of_nonneg x.pa
      split_ifs with h1 h2 h3 h4 h5
      ·
        ext
        · exact ha
        · cases h1
          expose_names
          simp_all
          exact (x.h h).symm
          expose_names
          cases h2
          simp_all
          expose_names
          exact (x.h h_1).symm
          simp_all
          expose_names
          absurd h_1
          apply Real.cos_eq_zero_iff_sin_eq.mp at h
          cases h
          positivity
          positivity
      ·
        simp_all
        cases h1
        expose_names
        absurd h3
        rw[h]
        simp
        expose_names
        ext
        ·
          rfl
        · apply Real.cos_eq_zero_iff.mp at h
          cases h
          · expose_names
            cases w with
            | ofNat n =>
              cases n with
              | zero =>
                simp_all
              | succ n =>
                exfalso
                have pθ := x.pθ
                have h' : ↑n + 1 ≥ 1 := by grind
                have h'' : (2 * (↑n + 1) + 1) * Real.pi / 2 ≥ (3 : ℕ) * (Real.pi / 2) := by
                  have h'' : ((2 : ℝ) * (n + (1 : ℝ)) + (1 : ℝ)) ≥ (3 : ℝ) := by
                    nlinarith
                  have hpi : 0 ≤ Real.pi / 2 := by
                    positivity
                  nlinarith
                have hpi' : (3 : ℝ) * (Real.pi / 2) > Real.pi := by
                  have hpi2 : 0 < Real.pi / 2 := by positivity
                  nlinarith [Real.pi_pos]
                rw [h_1] at pθ
                norm_num at pθ
                have : ¬ ((2 * (↑n + 1) + 1) * Real.pi / 2 < Real.pi) := by
                  nlinarith
                exact this pθ.2
            | negSucc n =>
              exfalso
              cases n with
              | zero =>
                have hxa0 : x.a ≠ 0 := by
                  intro hx0
                  apply h2
                  exact Or.inl hx0
                have hapos : 0 < x.a := by
                  exact lt_of_le_of_ne x.pa (Ne.symm hxa0)
                rw [h_1] at h3
                norm_num at h3
                have hs : Real.sin (-Real.pi / 2) = (-1 : ℝ) := by
                  simp [Real.sin_pi_div_two]
                rw [hs] at h3
                nlinarith
              | succ n =>
                have pθ := x.pθ
                rw [h_1] at pθ
                norm_num at pθ
                have hpi' : (3 : ℝ) * (Real.pi / 2) > Real.pi := by
                  have hpi2 : 0 < Real.pi / 2 := by positivity
                  nlinarith [Real.pi_pos]
                have : ((2 * (↑n + 1) + 1) * Real.pi / 2 : ℝ) > Real.pi := by
                  have h'' : ((2 : ℝ) * (n + (1 : ℝ)) + (1 : ℝ)) ≥ (3 : ℝ) := by nlinarith
                  nlinarith
                nlinarith [pθ.1, this]

      · grind
      ·
        ext
        · exact ha
        ·
          have hxa0 : x.a ≠ 0 := by
            exact left
          have hcos0 : Real.cos x.θ ≠ 0 := by
            exact right
          have hapos : 0 < x.a := by
            exact lt_of_le_of_ne x.pa (Ne.symm hxa0)
          have hcospos : 0 < Real.cos x.θ := by
            by_contra hc
            have hcle : Real.cos x.θ ≤ 0 := le_of_not_gt hc
            have hmul : x.a * Real.cos x.θ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos x.pa hcle
            linarith
          have hθlt : x.θ < Real.pi / 2 := by
            by_contra hnot
            have hge : Real.pi / 2 ≤ x.θ := le_of_not_gt hnot
            have hle : x.θ ≤ Real.pi := le_of_lt x.pθ.2
            have hnonpos : Real.cos x.θ ≤ 0 := Real.cos_nonpos_of_pi_div_two_le_of_le hge hle
            linarith
          have hθgt : -(Real.pi / 2) < x.θ := by
            by_contra hnot
            have hle : x.θ ≤ -(Real.pi / 2) := le_of_not_gt hnot
            have hge' : Real.pi / 2 ≤ -x.θ := by nlinarith
            have hle' : -x.θ ≤ Real.pi := by
              have hp := x.pθ.1
              nlinarith
            have hnonpos : Real.cos (-x.θ) ≤ 0 := Real.cos_nonpos_of_pi_div_two_le_of_le hge' hle'
            have hnonpos' : Real.cos x.θ ≤ 0 := by simpa [Real.cos_neg] using hnonpos
            linarith
          have hratio : x.a * Real.sin x.θ * (x.a * Real.cos x.θ)⁻¹ = Real.tan x.θ := by
            rw [Real.tan_eq_sin_div_cos, div_eq_mul_inv]
            field_simp [hxa0, hcos0]
          rw [show Real.arctan (x.a * Real.sin x.θ * (x.a * Real.cos x.θ)⁻¹) = x.θ by
            rw [hratio]
            exact Real.arctan_tan hθgt hθlt]
      · grind
      · grind

  )

}

end HW_III_6
