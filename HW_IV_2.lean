import Mathlib

namespace HW_IV_2

-- class Subtype {α : Sort u} (p : α → Prop)
--   val : α
--   property : p val

def Evens := Subtype (fun n => ∃ k, n = 2*k)
example : Evens := ⟨ 14, by use 7 ⟩


-- 1 ------------------------
def Evens.add (x y : Evens) : Evens := {
    val := x.val + y.val,
    property := by {
        have hx := x.property
        have hy := y.property
        cases hx with
        | intro a ha =>
            cases hy with
            | intro b hb =>
                use (a + b)
                simp_all only
                exact Eq.symm (Nat.mul_add 2 a b)
    }
}

def Evens.add_assoc {x y z : Evens} : add x (add y z) = add (add x y) z := by grind[add] --⛳️




universe u
variable (α β : Type u) {A B C : Set α} {D E : Set β}
-- 2 ------------------------
example : A ⊆ C → B ⊆ C → A ∪ B ⊆ C := by grind --but that would be cheating
example : A ⊆ C → B ⊆ C → A ∪ B ⊆ C := by
    intro h1 h2 a ha
    cases ha with
    | inl ha => exact h1 ha
    | inr ha => exact h2 ha

example : A ⊆ B → B ⊆ C → A ⊆ C := by
    intro h1 h2 a h3
    exact h2 (h1 h3)



-- 3 ------------------------
example {f : α → β} : f '' (A ∪ B) = f '' A ∪ f '' B := by
    unfold Set.instUnion
    unfold Union.union
    unfold Set.union
    unfold Set.image
    unfold Set.instMembership
    unfold Set.Mem
    simp only
    apply Set.ext
    intro x
    constructor
    ·   intro h
        simp only [Set.mem_setOf_eq] at h
        cases h with
        | intro a ha =>
            have hl := ha.left
            have hr := ha.right
            simp only [Set.mem_setOf_eq]
            cases hl with
            | inl hl =>
                left
                exact Exists.intro a ⟨hl, hr⟩
            | inr hl =>
                right
                exact Exists.intro a ⟨hl, hr⟩
    ·   intro h
        cases h with
        | inl h =>
            cases h with
            | intro a ha =>
                have hal := ha.left
                have har := ha.right
                simp only [Set.mem_setOf_eq]
                use a
                constructor
                ·   left
                    exact hal
                ·   exact har
        | inr h =>
            simp only [Set.mem_setOf_eq]
            cases h with
            | intro a ha =>
                have hal := ha.left
                have har := ha.right
                use a
                constructor
                ·   right
                    exact hal
                ·   exact har




-- 4 ------------------------
example {f : α → β} : f⁻¹' (D ∩ E) = f⁻¹' D ∩ f⁻¹' E := by
    unfold Set.preimage
    unfold Set.instInter
    unfold Set.inter
    unfold Inter.inter
    unfold Membership.mem
    unfold Set.instMembership
    unfold Set.Mem
    simp only
    apply Set.ext
    intro x
    constructor
    ·   exact id
    ·   exact id



-- 5 ------------------------
example : Fin 0 → False := by
    intro a
    cases a
    expose_names
    exact Nat.not_succ_le_zero val isLt

example (x : Fin 2) : x = 0 ∨ x = 1 := by
    cases x
    expose_names
    cases val with
    | zero => left; rfl
    | succ a => cases a with
        | zero => right; rfl
        | succ b => absurd isLt; exact of_decide_eq_false rfl

example (n : ℕ) (x y : Fin n) : x = y ↔ x.val = y.val := by
    constructor
    ·   intro h
        exact congrArg Fin.val h
    ·   intro h
        exact Fin.eq_of_val_eq h


-- 6 -----------------------
def equiv_subtype {n : ℕ} : Fin n ≃ { x : ℕ | x < n } := {
    toFun := fun a => ⟨a.val, a.isLt⟩
    invFun := fun a => ⟨a.val, a.property⟩
    left_inv := by
        intro a
        exact Fin.eq_of_val_eq rfl
    right_inv := by
        intro a
        cases a
        rfl
}

-- 7 -----------------------
theorem equiv_same_size {n m : ℕ} (eq : Fin n ≃ Fin m) : n = m := by
    have hcard : Fintype.card (Fin n) = Fintype.card (Fin m) := Fintype.card_congr eq
    simpa using hcard



end HW_IV_2
