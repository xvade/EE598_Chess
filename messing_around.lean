import Mathlib
import Lean
open Lean Meta Tactic


example (a b : ℕ): 1 + 1 + (a + b)^2 = 2 + a^2 + 2 * a * b + b^2 := by
  rw[(h: 1+1=2 := by rfl) -> 1]


namespace MyNat
inductive MyNat where
| zero : MyNat
| succ : MyNat → MyNat

def MyNat.add (a b : MyNat) : MyNat :=
  match a, b with
  | zero, x => x
  | succ x, y => MyNat.succ (MyNat.add x y)

def MyNat.mul (a b : MyNat) : MyNat :=
  match a, b with
  | zero, _ => zero
  | succ x, y => MyNat.add y (MyNat.mul x y)

def MyNat.exp (a b : MyNat) : MyNat :=
  match a, b with
  | _, zero => MyNat.succ MyNat.zero
  | x, succ y => MyNat.mul x (MyNat.exp x y)


-- crashes the server if run
-- #eval MyNat.exp (MyNat.succ^[5] MyNat.zero) (MyNat.succ^[1000] MyNat.zero)
end MyNat


example (p q : ℕ) : (Real.sin p)^2 + (Real.cos p)^2 = 1 := by
  simp
