import Mathlib

-- 2
def h := λ (x : Nat) ↦ x^2

-- 3
#eval h (h (h 2))

-- 4
def Ω := λ x => x x  -- We get a type error. Lean insists that a function and its arguments have distinct types, but x has the same type as x.

-- 5
-- Questions:
-- 1. When attempting to verify programs not written in Lean, I would imagine that the weak link is the extent to which the representation of that program in Lean is accurate to the real world. How do people approach this problem? Is it fully solved?
-- 2. Not all proof assistants are also programming languages, what makes that a good idea?
-- 3. At the moment, Lean is mostly for mathematicians, and also a little bit for software engineers. Who is it for in the long run?
