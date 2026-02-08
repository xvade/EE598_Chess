import Mathlib

namespace HW_III_5

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

end HW_III_5

