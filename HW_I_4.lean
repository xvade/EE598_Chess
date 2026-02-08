import Mathlib
set_option linter.style.longLine false
----------------------------------------------------------------------
inductive MyNat where
  | zero : MyNat
  | succ : MyNat → MyNat

-- open MyNat

#check MyNat.zero
#check MyNat.zero.succ
----------------------------------------------------------------------
-- Slide 8

-- 1
inductive MyComplex where
  | mkMagArg : NNReal → Real → MyComplex
  -- | mkRealIm : ℝ → ℝ → MyComplex  -- this was harder than I expected

open MyComplex

def MyComplex.arg (x : MyComplex) : Real :=
  match x with
  | mkMagArg _ x => x
  -- | mkRealIm x y =>

def MyComplex.mag (x : MyComplex) : NNReal :=
  match x with
  | mkMagArg x _ => x
  -- | mkRealIm x y => NNReal.sqrt (x^2 + y^2)
  -- TODO: how to do a range between 0 and 2π as an argument? probably a type for that


-- 2
inductive TriBool where
  | T : TriBool
  | F : TriBool
  | U : TriBool

open TriBool

def and (A B : TriBool) :=
  match A, B with
  | T, x   => x
  | F, _   => F
  | U, F   => F
  | U, _   => U

def or (A B : TriBool) :=
  match A, B with
  | T, _ => T
  | F, x => x
  | U, T => T
  | U, _ => U

#eval and T (and U F)   -- F


-- 3
def reciprocal (x : ℚ) : Option ℚ :=
  match x with
  | 0 => .none
  | _ => .some (if x > 0 then x.den / (Int.toNat x.num) else x.den / (Int.toNat (-x.num)))


-----------------------------------------------------------------
-- Slide 14
inductive BTree (A : Type) where
  | leaf : A → BTree A
  | node : A → BTree A → BTree A → BTree A

namespace BTree

def to_list {A : Type} (T : BTree A) : List A :=
  match T with
  | leaf a => [a]
  | node a left right => [a] ++ (to_list left) ++ (to_list right)

def to_str {A : Type} [sa : ToString A] (T : BTree A) : String :=
  match T with
  | leaf a => toString a
  | node a L R =>  "(" ++ (toString a) ++ " " ++ (to_str L) ++ " " ++ (to_str R) ++ ")"

instance {A : Type} [Repr A] [ToString A] : Repr (BTree A) := {
  reprPrec := fun T _ => to_str T
}

def map {A B : Type} (f : A → B) (T : BTree A) : BTree B :=
  match T with
  | leaf a => leaf (f a)
  | node a left right => node (f a) (map f left) (map f right)

-- 4
def swap {A : Type} (T : BTree A) : BTree A :=
  match T with
  | leaf a      => leaf a
  | node  a L R => node a (swap R) (swap L)

end BTree
#eval BTree.node 0 (BTree.leaf 0) (BTree.leaf 0)



-----------------------------------------------------------------
-- Slide 17

mutual
  inductive Term
  | var : String → Term
  | num : ℕ → Term
  | paren : Expr → Term

  inductive Expr
  | neg : Term → Expr
  | add : Term → Term → Expr
  | mul : Term → Term → Expr
end

-- 5
mutual
  def Term.countAdds (t : Term) : ℕ :=
    match t with
    | .var _ => 0
    | .num _ => 0
    | .paren e => Expr.CountAdds e

  def Expr.CountAdds (e : Expr) : ℕ :=
    match e with
    | .neg a => Term.countAdds a
    | .add a b => Term.countAdds a + Term.countAdds b + 1
    | .mul a b => Term.countAdds a + Term.countAdds b
end
-----------------------------------------------------------------
structure Komplex where
  re : Real
  im : Real

def conj (x : Komplex) : Komplex := {
  re := x.re,
  im := -x.im
}

def negate1 (x : Komplex) : Komplex :=
  match x with  | Komplex.mk a b => ⟨ -a, -b ⟩

def negate2 (x : Komplex) : Komplex :=
  match x with | ⟨ a, b ⟩ => ⟨ -a, -b ⟩


structure A where
  x : ℕ

structure B where
  x : ℕ

structure C extends A, B where
  z : ℕ

instance : Repr C := {
  reprPrec := fun a _ => a.x.repr
}

def C.ToExpr := ""
variable (c : C)
#eval C.mk (A.mk 5) 8

-- 6
structure Vector3D where
  x : ℚ
  y : ℚ
  z : ℚ

-- 7
def Vector3D.cross (a b : Vector3D) : Vector3D :=
  Vector3D.mk (a.y * b.z + a.z * b.y) (- a.x * b.z - a.z * b.x) (a.x * b.y + a.y * b.x)

#eval Vector3D.cross (Vector3D.mk 0 0 0) (Vector3D.mk 1 1 1)
#eval Vector3D.cross (Vector3D.mk 1 0 0) (Vector3D.mk 0 2 0)

-- 8
def crossProd (a b : ℚ × ℚ × ℚ) : ℚ × ℚ × ℚ :=
  ⟨a.snd.fst * b.snd.snd + a.snd.snd * b.snd.fst,
  - a.fst * b.snd.snd - a.snd.snd * b.fst,
  a.fst * b.snd.fst + a.snd.fst * b.fst⟩

#eval crossProd ⟨0, 0, 0⟩ ⟨1, 1, 1⟩
#eval crossProd ⟨1, 0, 0⟩ ⟨0, 2, 0⟩

-- 9
def Shape := ℚ ⊕ (ℚ × ℚ)

def Shape.area (s : Shape) : ℚ :=
  match s with
  | .inl radius => 3.14 * radius ^ 2
  | .inr corner => corner.fst * corner.snd

def Shape.perimiter (s : Shape) : ℚ :=
  match s with
  | .inl radius => 6.28 * radius
  | .inr corner => 2 * (corner.fst + corner.snd)

-----------------------------------------------------------------
-- Slide 39

-- 10
structure MyTree (T : Type) where
  val : T
  children : List (MyTree T)


#check MyTree.mk 0 []
#check MyTree.mk 2 [MyTree.mk 0 [], MyTree.mk 6 [MyTree.mk 0 []], MyTree.mk 20 []]
#check MyTree.mk "strings work too" [MyTree.mk "and the children will have strings" []]
#check_failure MyTree.mk "but everything has to have the same type" [MyTree.mk "so even if the child of a child has the wrong type, it won't work" [MyTree.mk (0 : ℕ) []]]

-- 11
def MyTree.apply {T₀ T₁ : Type} (f : T₀ → T₁) : MyTree T₀ → MyTree T₁
  | ⟨a, L⟩ => ⟨f a, L.map (MyTree.apply f)⟩

-- 12
def BTree_to_MyTree {T : Type} : BTree T → MyTree T
  | BTree.leaf val => MyTree.mk val []
  | BTree.node val l r => MyTree.mk val [BTree_to_MyTree l, BTree_to_MyTree r]

#eval BTree_to_MyTree (BTree.leaf 0)
#eval BTree_to_MyTree (BTree.node 1 (BTree.leaf 0) (BTree.leaf 0))
#eval BTree_to_MyTree (BTree.node "works with strings too" (BTree.node "" (BTree.leaf "a") (BTree.leaf "b")) (BTree.leaf "0"))
-----------------------------------------------------------------
-- Slide 40

-- 13
namespace Temp
inductive Dyadic where
  | zero    : Dyadic
  | add_one : Dyadic → Dyadic  -- x ↦ x + 1
  | half    : Dyadic → Dyadic  -- x ↦ x / 2
  | neg     : Dyadic → Dyadic  -- x ↦ -x

-- a
def Double : Dyadic → Dyadic
  | .zero      => .zero
  | .add_one a => .add_one (.add_one (Double a))
  | .half a    => a
  | .neg a     => .neg (Double a)

-- b
def depth : Dyadic → ℕ  -- helper function for showing termination of add
  | .zero => 0
  | .add_one a => 1 + depth a
  | .half a => 2 + depth a
  | .neg a => 1 + depth a


def add (a : Dyadic) (b : Dyadic) :=  -- there has GOT to be a better way to do this, but I didn't find it.
  match a, b with
  | .zero, x                   => x
  | .add_one x, y              => .add_one (add x y)
  | .half x, .zero             => .half x
  | .half x, .add_one y        => .add_one (add (.half x) y)
  | .half x, .half y           => .half (add x y)
  | .half x, .neg .zero        => .half x
  | .half x, .neg (.add_one y) => add x (.neg (.add_one (.add_one y)))
  | .half x, .neg (.half y)    => .half (add x (.neg y))
  | .half x, .neg (.neg y)     => add (.half x) y
  | .neg x, .zero              => .neg x
  | .neg x, .add_one y         => .add_one (add (.neg x) y)
  | .neg .zero, .half y        => .half y
  | .neg (.add_one x), .half y => add y (.neg (.add_one (.add_one x)))
  | .neg (.half x), .half y    => .half (add y (.neg x))
  | .neg (.neg x), .half y     => add (.half y) x
  | .neg x, .neg y             => .neg (add x y)
  termination_by depth a + depth b decreasing_by
    all_goals repeat rw[depth]
    all_goals linarith


def add' (a : Dyadic) (b : Dyadic) := -- here's the better way to do it, I was messing up with .neg. Better way courtesy of Evan. I am kind of glad in a way I got an opportunity to play with termination_by though.
match a, b with
| .zero, y => y
| .add_one x, y => .add_one (add' x y)
| .half x, y => .half (add' x (Double y))
| .neg x, y => .neg (add' x (.neg y))

-- c
def mul (a : Dyadic) (b : Dyadic) :=
  match a, b with
  | .zero, _ => Dyadic.zero
  | .add_one x, y => add y (mul x y)
  | .half x, y => .half (mul x y)
  | .neg x, y => .neg (mul x y)

-- d
def to_rat (a : Dyadic) : ℚ :=
  match a with
  | .zero => 0 / 1
  | .add_one x => (to_rat x) + 1
  | .half x => (to_rat x) / 2
  | .neg x => - (to_rat x)

-- e

def five_eighths : Dyadic := add (.half (.add_one .zero)) (.half (.half ((.half (.add_one .zero)))))
#eval to_rat five_eighths
def negative_seven_thirty_seconds : Dyadic := .neg (.half (.half (.half (.half (.half (.add_one (.add_one (.add_one (.add_one (.add_one (.add_one (.add_one .zero))))))))))))
#eval to_rat negative_seven_thirty_seconds
#eval to_rat (add five_eighths negative_seven_thirty_seconds)
#eval add negative_seven_thirty_seconds five_eighths
#eval to_rat (add negative_seven_thirty_seconds five_eighths)
#eval to_rat (mul five_eighths negative_seven_thirty_seconds)
#eval to_rat (mul negative_seven_thirty_seconds five_eighths)
#eval mul negative_seven_thirty_seconds five_eighths
-- f

-- Dyadics as defined here are not unique--or rather, `to_rat x` is not unique for all Diadics x. We can see this with something as simple as
#eval to_rat (.zero)
#eval to_rat (.half .zero)
-- `.zero` and `.half .zero` are stored as different values even though they have the same `to_rat`.
end Temp
