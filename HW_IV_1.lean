import Mathlib

namespace HW_IV_1
universe u

class Group (G : Type u) where
  op : G → G → G                                    -- data
  e : G
  assoc {a b c} : op (op a b) c = op a (op b c)     -- properties
  id_left {a} : op e a = a
  inv : G → G
  inv_left {a} : op (inv a) a = e

class CommGroup (G : Type u) extends Group G where
  comm {a b} : op a b = op b a                      -- additional property

infixl:60 " + " => Group.op            -- left associating infix syntax
prefix:95 "-" => Group.inv

open Group CommGroup

variable (G : Type u) [Group G] (a b c : G)

@[simp]
theorem Group.id_inv_left {G : Type u} [Group G] {a : G}
  : e + (-a) = -a
  := by rw[id_left]

theorem Group.cancel_left : a + b = a + c → b = c := by
  intro h
  apply congrArg (fun t => -a + t) at h
  rw[←assoc] at h
  rw[inv_left] at h
  rw[id_left] at h
  rw[←assoc] at h
  rw[inv_left] at h
  rw[id_left] at h
  exact h

@[simp]
theorem Group.id_right : a + e = a := by
  apply cancel_left (a := -a)
  calc  -a +  (a + e)
  _   = (-a + a) + e   := by rw[assoc]
  _   = (e + e : G)    := by rw[inv_left]
  _   = e              := by rw[id_left]
  _   = -a + a         := by rw[inv_left]

@[simp]
theorem Group.id_left_for_simp {H : Type u} [Group H] (d : H) : e + d = d := id_left

@[simp]
theorem Group.inv_left_for_simp {H : Type u} [Group H] (d : H) : -d + d = e := inv_left

@[simp]
theorem Group.inv_right : a + (-a) = e := by
  apply cancel_left (a := -a)
  calc  -a + (a + (-a))
  _   = (-a + a) + (-a) := by rw[assoc]
  _   = e + (-a)        := by rw[inv_left]
  _   = -a              := by rw[id_left]
  _   = -a + e          := by rw[id_right (a := -a)]

-- 1 ------------------------
theorem Group.id_unique {e' : G} : (∀ a, e'+ a = a) → e = e' := by
    intro h
    have h2 : e' + e = e' := by simp
    have h3 : e' + e = e := h e
    rw[← h2]
    nth_rewrite 1 [← h3]
    rfl

-- 2 ------------------------
theorem Group.inv_unique : b + a = e → c + a = e → b = c := by
    intro h1 h2
    rw[← h2] at h1
    apply congrArg (fun t => t + -a) at h1
    rw[assoc, assoc, inv_right, id_right, id_right] at h1
    exact h1




inductive Spin where | up | dn
open Spin

def Spin.toggle : Spin → Spin
  | up => dn
  | dn => up

def op (x y : Spin) : Spin := match x, y with
  | up,dn => dn
  | dn,up => dn
  | _,_ => up

instance Spin.inst_comm_group : CommGroup Spin := {
  op := op,
  e := up,
  inv := id,
  assoc {a b c} := by cases a <;> cases b <;> cases c <;> aesop,
  id_left {a}   := by cases a <;> aesop
  inv_left {a}  := by cases a <;> aesop
  comm {a b}    := by cases a <;> simp[op] <;> aesop
}

example : up + dn = dn + up := by exact comm


-- 3 ------------------------
instance Group.prod {G H : Type u} [Group G] [Group H] : Group (G × H) := {
  op x y := (x.1 + y.1, x.2 + y.2),
  e := (e,e),
  inv x := (-x.1, -x.2),
  id_left {x} := by simp,
  inv_left := by simp,
  assoc := by simp [assoc]
}

infix:50 " × " => Group.prod


-- 4 ------------------------
example : e = (up,up) := by
    unfold e
    unfold prod
    simp
    rfl

example : -(up,up) = (up,up) := by
    rw[inv]
    rw[prod]
    simp
    rfl

lemma cross_spin (x : Spin × Spin) : - x + x = (up,up) := by aesop

class Monoid (M : Type u) where
  mul : M → M → M
  one : M
  mul_assoc {a b c : M} : mul (mul a b) c = mul a (mul b c)
  mul_id_left {a : M}   : mul one a = a
  mul_id_right {a : M}  : mul a one = a

@[simp] theorem mul_id_left_for_simp {a : M} [Monoid M] : Monoid.mul Monoid.one a = a :=
    Monoid.mul_id_left

class Ring (R : Type u)
  extends CommGroup R, Monoid R where
  l_distrib {x y z : R} : mul x (op y z) = op (mul x y) (mul x z)
  r_distrib {x y z : R} : mul (op y z) x = op (mul y x) (mul z x)

class CommRing (R : Type u)
   extends Ring R where
   mul_comm {x y : R} : mul x y = mul y x

variable {R : Type u} [CommRing R]

infixl:80 " * " => Monoid.mul

def Group.sub (x y : R):= Group.op x (-y)
infixl:60 " - " => Group.sub

open Monoid Ring CommRing

@[simp] theorem Ring.add_left  (h : y = z) (x : R) : x + y = x + z := by rw [h]
@[simp] theorem Ring.add_right (h : y = z) (x : R) : y + x = z + x := by rw [h]
@[simp] theorem Ring.mul_left  (h : y = z) (x : R) : x * y = x * z := by rw [h]
@[simp] theorem Ring.mul_right (h : y = z) (x : R) : y * x = z * x := by rw [h]

@[simp]
theorem mul_zero {R : Type u} [CommRing R] (x : R) : x * e = e := by
  have h0 := l_distrib (x := x) (y := e) (z := e)
  have h := Ring.add_left h0 (-(x*e))
  rw[id_left]  at h
  rw[inv_left] at h
  rw[←assoc]   at h
  rw[inv_left] at h
  rw[id_left]  at h
  exact h.symm

@[simp]
theorem zero_mul {R : Type u} [CommRing R] (x : R) : e * x = e := by
    rw[CommRing.mul_comm]
    exact mul_zero x

@[simp]
theorem neg_one {R : Type u} [CommRing R] (x : R) : (-one:R)*x = -x := by
  have h0 : (one:R) + -(one:R) = (e:R) := by rw[inv_right]
  have h1 : e = (e:R) * x := by rw[CommRing.mul_comm,mul_zero]
  nth_rewrite 2 [←h0] at h1
  rw[r_distrib,mul_id_left] at h1
  have h2 := add_left h1 (-x)
  rw[←assoc,id_right,inv_left,id_left] at h2
  exact h2.symm


-- 5 ------------------------
theorem factor_mul_inv_right (x y : R) : x * (-y) = -(x*y) := by
    rw[← neg_one, ←Monoid.mul_assoc]
    nth_rewrite 2 [CommRing.mul_comm]
    rw[Monoid.mul_assoc]
    simp


def Spin.mul (a b : Spin) : Spin :=
  match a, b with
  | dn, dn => dn
  | _, _ => up

instance Spin.inst_monoid : Monoid Spin := {
  one := dn,
  mul := Spin.mul
  mul_assoc {x y z} := by cases x <;> cases y <;> cases z <;> aesop
  mul_id_left {x}   := by cases x <;> simp[Spin.mul]
  mul_id_right {x}  := by cases x <;> simp[Spin.mul]
}

instance Spin.inst_ring : Ring Spin := {
  l_distrib {x y z} := by cases x <;> cases y <;> cases z <;> aesop
  r_distrib {x y z} := by cases x <;> cases y <;> cases z <;> aesop
}

-- 6 ------------------------
example (x y : Spin) : x*y + x = x*(y+dn) := by
    nth_rewrite 2 [(@Spin.inst_monoid.mul_id_right x).symm]
    exact l_distrib.symm






instance Seq.inst_group {R : Type u} [Ring R] : Group (ℕ → R) := {
  op f g n      := f n + g n,
  e n           := e,
  inv f n       := - f n,
  assoc {f g h} := by funext n; exact assoc,
  id_left {f}   := by funext n; exact id_left,
  inv_left {f}  := by funext n; exact inv_left
}



instance Seq.inst_monoid {R : Type u} [Ring R] : Monoid (ℕ → R) := {
  mul f g n := (f n) * (g n),
  one n := one,
  mul_assoc {f g h} := by funext n; exact mul_assoc,
  mul_id_left {f}   := by funext n; rw[mul_id_left]
  mul_id_right {f}  := by funext n; rw[mul_id_right]
}


-- 7 ------------------------
instance Seq.inst_ring {R : Type u} [Ring R] : Ring (ℕ → R) := {
    comm {x y} := by funext n; exact comm
    l_distrib {x y z} := by funext n; exact l_distrib
    r_distrib {x y z} := by funext n; exact r_distrib
}

-- 8 ------------------------
example : CommRing R → CommRing (ℕ → R) := fun h => {
    mul_comm := by
        intro x y
        funext n
        exact mul_comm
}




structure Ideal (R : Type u) [CommRing R] where
  I : R → Prop
  has_zero : I e
  closed {x y : R} : I x → I y → I (-x + y)
  absorb {r x : R} : I x → I (r * x) ∧ I (x * r)


-- 9 ------------------------
def PrincipalIdeal {R : Type u} [CommRing R] (a : R) : Ideal R := {
  I b := ∃ r : R, b = a * r,
  has_zero := by {
    use ((e:R) + ((Group.inv one) * (e:R)))
    simp
  }
  closed := by {
    intro x y h1 h2
    cases h1 with
    | intro c hc =>
        cases h2 with
        | intro d hd =>
            use (d - c)
            rw[hc, hd]
            rw[Group.sub, l_distrib, CommGroup.comm]
            nth_rewrite 2 [←neg_one]
            rw[←Monoid.mul_assoc]
            nth_rewrite 5 [CommRing.mul_comm]
            rw[Monoid.mul_assoc]
            simp
  },
  absorb := by {
    intro r x h1
    cases h1 with
    | intro r0 h1
    constructor
    ·   use (r * r0)
        rw[h1]
        rw[←Monoid.mul_assoc]
        nth_rewrite 2 [CommRing.mul_comm]
        rw[Monoid.mul_assoc]
    ·   rw[h1]
        use (r0 * r)
        rw[Monoid.mul_assoc]
  }
}


class Nontrivial (α : Type*) : Prop where
  exists_pair_ne : ∃ x y : α, x ≠ y

class Field (F : Type u) extends CommRing F, Nontrivial F where
  minv : F → F
  minv_zero : minv e = e
  mul_inv_prop {x : F} : x ≠ e → mul x (minv x) = one

open Field

variable {F : Type u} [Field F] {x y z : F}

postfix:95 "⁻¹" => Field.minv

section
variable (x y : F)
#check one * (x - x⁻¹) + e * y
end

@[simp]
theorem mul_id_right : x * one = x := by
  rw[CommRing.mul_comm]
  rw[mul_id_left]

theorem one_ne_e : (one:F) ≠ e := by
  intro h
  obtain ⟨ x, y, hxy ⟩ := (inferInstance : Nontrivial F).exists_pair_ne
  have hx : x = e := by
    calc
      x = x * one := by rw[mul_id_right]
      _ = x * e   := by rw[h]
      _ = e       := by rw [mul_zero]
  have hy : y = e := by
    calc
      y = y * one := by rw[mul_id_right]
      _ = y * e   := by rw[h]
      _ = e       := by rw[mul_zero]
  exact hxy (hx.trans hy.symm)


instance Spin.inst_nt : Nontrivial Spin := {
  exists_pair_ne := by
    use up, dn
    simp
}

instance Spin.inst_comm_ring : CommRing Spin := {
  mul_comm {x y} := by cases x <;> cases y <;> aesop
}

instance Spin.inst_field : Field Spin := {
  minv x := x
  minv_zero := by simp,
  mul_inv_prop {x} h := by cases x <;> simp_all[e]; rfl
}

-- 10 -----------------
theorem one_inv : (one:F)⁻¹ = one := by
    nth_rewrite 2 [←(Field.mul_inv_prop one_ne_e)]
    simp

-- 11 -----------------
instance int_commring : CommRing ℤ := {
    op := Int.add
    e := 0
    assoc {a b c} := Int.add_assoc a b c
    id_left {a} := Int.zero_add a
    inv {a} := -a
    inv_left {a} := Int.add_left_neg a
    comm {a b} := Int.add_comm a b
    mul := Int.mul
    one := 1
    mul_assoc {a b c} := Int.mul_assoc a b c
    mul_id_left {a} := Int.one_mul a
    mul_id_right {a} := Int.mul_one a
    l_distrib {a b c} := Int.mul_add a b c
    r_distrib {a b c} := Int.add_mul b c a
    mul_comm {a b} := Int.mul_comm a b
}



@[simp]
theorem minv_zero_for_simp : (e : F)⁻¹ = e := minv_zero

@[simp]
theorem minv_minv (x : F) : x⁻¹⁻¹ = x := by
    by_cases h : x = e
    ·   rw[h]
        simp
    ·   have h1 : x * x⁻¹ = one := mul_inv_prop h
        have h3 : x⁻¹ ≠ e := by
            intro h0
            have h2 := congrArg (fun a => x * a) h0
            simp only [mul_zero] at h2
            rw[mul_inv_prop h] at h2
            exact one_ne_e h2
        have h2 := Field.mul_inv_prop h3
        rw[←h1, CommRing.mul_comm] at h2
        have h4 := congrArg (fun (a : F) => x * a) h2
        simp only at h4
        nth_rewrite 2 [CommRing.mul_comm] at h4
        nth_rewrite 4 [CommRing.mul_comm] at h4
        rw[←Monoid.mul_assoc, ←Monoid.mul_assoc] at h4
        simp_all


-- 12 ----------------
theorem inverse_mul (a b : F) : (a * b)⁻¹ = a⁻¹ * b⁻¹ := by
    by_cases h : (a * b)⁻¹ = e
    ·   have h1 : (a * b)⁻¹ = (a * b) := by
            have h1 := congrArg (fun x => (a * b) * x) h
            simp only [mul_zero] at h1
            by_cases h2 : (a * b) = e
            ·   rw[h, h2]
            ·   have h3 := Field.mul_inv_prop h2
                rw[h3] at h1
                exfalso
                exact one_ne_e h1
        rw[h]
        by_cases h2 : a = e
        ·   rw[h2, minv_zero]
            simp
        ·   rw[h] at h1
            have h3 := congrArg (fun x => a⁻¹ * x) h1
            simp only [mul_zero] at h3
            rw[←Monoid.mul_assoc] at h3
            nth_rewrite 2 [CommRing.mul_comm] at h3
            rw[mul_inv_prop h2] at h3
            simp only [mul_id_left_for_simp] at h3
            rw[←h3]
            rw[minv_zero]
            simp
    ·   have h1 := Field.mul_inv_prop h
        rw[minv_minv] at h1
        have ha : a ≠ e := by
            intro h2
            rw[h2] at h
            simp at h
        have hb : b ≠ e := by
            intro h2
            rw[h2] at h
            simp at h
        have h2 : (a⁻¹ * b⁻¹) * (a * b) = one := by
            rw[Monoid.mul_assoc]
            nth_rewrite 3 [CommRing.mul_comm]
            nth_rewrite 2 [←Monoid.mul_assoc]
            nth_rewrite 3 [CommRing.mul_comm]
            rw[Field.mul_inv_prop hb]
            simp only [mul_id_left_for_simp]
            rw[CommRing.mul_comm]
            rw[Field.mul_inv_prop ha]
        rw[←h2] at h1
        have h3 := congrArg (fun x => x * (a * b)⁻¹) h1
        simp only at h3
        have h4 : a * b ≠ e := by
            intro h4
            have h5 := congrArg minv h4
            rw[←minv_zero, minv_minv] at h5
            exact h h5
        rw[Monoid.mul_assoc, Field.mul_inv_prop h4, Monoid.mul_assoc, Field.mul_inv_prop h4] at h3
        simp only [mul_id_right] at h3
        exact h3



end HW_IV_1
