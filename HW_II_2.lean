import Mathlib
set_option linter.style.longLine false


-- 1
universe u v
#check Type u ⊕ Type v  -- Type (max (u + 1) (v + 1)), it knows that it needs room for both.

-- 2
namespace Temp
def TypeList := List Type

#check TypeList
def A : TypeList := [] -- This is fine because the empty list is always going to be valid term of a list type.
def B : TypeList := [TypeList] -- This is not fine because TypeList has type Type 1, which is not Type 0, the expected type of members of a TypeList.
def C : TypeList := [ℕ,ℚ] -- This is fine because it is a list with members of Type 0, the intended use of the TypeList.
#check Type u × Type v
def D : TypeList := [ℕ,ℕ×Type] -- This is not fine because Type has type Type 1, causing the whole product to have type Type 1, which is not Type 0, the appropriate type for a member of a TypeList.
#check List (Type u)
def E : TypeList := [ℕ,List ℕ] -- This is fine because List inherits its type from its argument, and ℕ is clearly of Type 0.
#check Prop
#check Sort 0
def F : TypeList := [ℕ,ℕ×Prop] -- This is fine because Prop and ℕ both have type Type, so their product is also a Type.
#check TypeList
def G : TypeList := [ℕ,G] -- G is an object of type TypeList, which is not Type, and therefore cannot be contained within TypeLists.
end Temp

-- 3
namespace Temp2
def TypeList.{w} := List (Type w)
-- To start with, it makes sense that everything that worked before still works, since the checker can infer w to be 0 in those cases.
def A : TypeList := []
def B : TypeList := [TypeList] -- The reason this works now has to do with the polymorphism. The first instance of TypeList is inferred to have a different type from the second instance. We've allowed the checker to do this by making TypeList polymorphic. Notably, it is not the same as
def B' : TypeList.{u} := [TypeList.{u}] -- B' doesn't work since a `List` of `Type u`s must have type `u+1`, but I'm trying to put something of type `u` in it.
#check TypeList
#check B
def C : TypeList := [ℕ,ℚ]
def D : TypeList := [ℕ,ℕ×Type] -- This still doesn't work, since ℕ and ℕ×Type have different types, so even with the polymorphism, there's no possible type for D that makes this ok. Notably the follwing works
def D' : TypeList := [ℕ×Type]
def E : TypeList := [ℕ,List ℕ]
def F : TypeList := [ℕ,ℕ×Prop]
def G : TypeList := [ℕ,G] -- Because the first entry is ℕ, Lean infers that the elements of G must be of type Type, so G must be of type Type 1. It then encounters G, which is not of type Type, and fails.
def G' : TypeList := [G'] -- I think this example is a little more interesting than the previous. Now instead of wrestling with the fact that an object of type Type 1 is not of type Type 0, Lean fails because an object of type Type (u+1) is not of type Type u, regardless of the value of u.
end Temp2

-- 4
def f (n : ℕ) := if n = 0 then Type u else Type u -- This does not type check because Lean can infer from the `then` clause that f has type `ℕ → Type 1`, but then the `else` clause attempts to produce something of type Type 2.
def f'.{n} := Type n -- This is close to the right idea, but it doesn't capture the essential thought of converting a natural to a universe. I haven't been able to find a way to do that

variable (a : ℕ)
