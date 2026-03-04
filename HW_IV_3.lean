import Mathlib

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
    · intro h1
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
  · intro h
    cases h with
    | base h1 =>
      induction h1 with
      | base h2 =>
        exact TransC.base (ReflC.base h2)
      | trans hxy hyz ih =>
        exact TransC.trans (ReflC.base hxy) ih
    | refl =>
      exact TransC.base ReflC.refl
  · intro h
    induction h with
    | base h1 =>
      cases h1 with
      | base h2 =>
        exact ReflC.base (TransC.base h2)
      | refl =>
        exact ReflC.refl
    | trans hxy hyz ih =>
      cases hxy with
      | base hxyR =>
        cases ih with
        | base hyzTC =>
          exact ReflC.base (TransC.trans hxyR hyzTC)
        | refl =>
          exact ReflC.base (TransC.base hxyR)
      | refl =>
        simpa using ih


def subseq {α : Type u} (σ τ : ℕ → α) :=
  ∃ f, StrictMono f ∧ σ = τ ∘ f

-- 6 -----------------
example {α : Type u} : Trans (@subseq α) := by
  unfold Trans
  intro f g h s1 s2
  unfold subseq
  unfold subseq at s1
  unfold subseq at s2
  cases s1 with
  | intro f1 h1 =>
    cases s2 with
    | intro f2 h2 =>
      use f2 ∘ f1
      constructor
      · have h2l := h2.left
        have h1l := h1.left
        exact StrictMono.comp h2l h1l
      have hcomp : h ∘ f2 ∘ f1 = (h ∘ f2) ∘ f1 := by rfl
      simp_all

example {α : Type u} : Refl (@subseq α) := by
  unfold Refl
  intro f
  unfold subseq
  use id
  constructor
  · exact fun ⦃a b⦄ a_1 ↦ a_1
  rfl

example : ¬AntiSymm (@subseq ℕ) := by
  intro h
  unfold AntiSymm at h
  let s : ℕ → ℕ := fun n => n % 2
  let t : ℕ → ℕ := fun n => (n + 1) % 2
  have hs : subseq s t := by
    unfold subseq
    refine ⟨fun n => n + 1, ?_, ?_⟩
    · exact StrictMono.add_const (fun ⦃a b⦄ hab => hab) 1
    · funext n
      simp [s, t, Function.comp, Nat.add_assoc]
  have ht : subseq t s := by
    unfold subseq
    refine ⟨fun n => n + 1, ?_, ?_⟩
    · exact StrictMono.add_const (fun ⦃a b⦄ hab => hab) 1
    · rfl
  have hst : s = t := h s t hs ht
  have h1 : (0 : ℕ) = 1 := by
    have hEval := congrArg (fun f => f 0) hst
    simpa [s, t] using hEval
  exact Nat.zero_ne_one h1


end HW_IV_3
