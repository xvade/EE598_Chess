import Mathlib

namespace HW_II_5
-- 1

-- Type Inference: Show that the expression fun x => fun f => f x has type A → (A → B) → B for some types A and B using a derivation tree like the one on slide 6 of this slide deck.

/-
fun x => fun f => f x
Since x and f must be terms of some types, we will say that x:A and f:C.
Using ABST twice with hypothized types A, B, and C we get
x : A   ⊢  fun f => f x : B
x : A, f : C   ⊢  f x : B
Next we use the APPL rule with M = f, N = x, σ = A, τ = B
x : A, f : C  ⊢  f : A → B
x : A, f : C  ⊢  x : A
These judgements would hold if C were equal to A → B. Using the APPL rule we get
x : A, f : A → B ⊢ f x : B
So applying ABST twice more gives us
x : A, f : A → B, fx : B ⊢ fun x => fun f => f x : A → (A → B) → B
-/


-- 2


inductive Vec (α : Type) : Nat → Type where
  | nil  : Vec α 0
  | cons {n} :  α → Vec α n → Vec α (n + 1)

def Vec.default (n : ℕ) : Vec ℕ n :=
  match n with
  | 0 => Vec.nil
  | k+1 => Vec.cons 0 (Vec.default k)


def g1 : ℕ → Vec ℕ 0 := fun _ => Vec.nil
def g2 : Σ n, Vec ℕ n := ⟨0, Vec.nil⟩
def g3 : Π f : ℕ → ℕ, Σ n, Vec ℕ (f n) := fun (f : ℕ → ℕ) => ⟨0, Vec.default (f 0)⟩
def g4 : Σ A, Π B, Vec A B := ⟨ℕ, fun b => Vec.default b⟩

end HW_II_5
