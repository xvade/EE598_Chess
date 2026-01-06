import Mathlib

-----------------------------------------------------------------------
theorem T₁:∀x:ℝ, 0 ≤ x²:=sorry
-----------------------------------------------------------------------
#check (4,5)
#check ℕ×ℕ
#check Type
-----------------------------------------------------------------------
example (p q r : Prop) : (p → q) ∧ (q → r) → (p → r) := by
  aesop
-----------------------------------------------------------------------
def remove_zeros (L : List ℕ) : List ℕ := match L with
  | [] => List.nil
  | x::Q => if x = 0 then remove_zeros Q else x::(remove_zeros Q)

def square (L : List ℕ) : List ℕ := match L with
  | [] => List.nil
  | x::Q => x^2::(square Q)

#eval square [1,2,4,5,2,6]
-----------------------------------------------------------------------
#eval [7, 6, 5, 8, 1, 2, 6].find? (· < 5) = some 1
#eval [7, 6, 5, 8, 1, 2, 6].find? (· < 1) = none
