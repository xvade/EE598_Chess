
import Mathlib
set_option linter.style.longLine false
namespace HW_II_4
#check Nat.rec


-- 1
structure Pair (α : Type u) (β : Type v) where
  fst : α
  snd : β

-- instance {α β} [Repr α] [ToString α] [Repr β] [ToString β] : Repr (Pair α β) :=
  -- reprPrec := fun T _ => fun p => "Pair(" ++ toString p.fst ++ ", " ++ p.snd ++ ")"

#check Pair.mk 0 Type

-- 2
def swap_pair (p : Pair α β) : Pair β α := Pair.mk p.snd p.fst

#check swap_pair (Pair.mk 0 Type)
#check swap_pair

-- 3
def chooseType : Bool → Type
| true  => Nat
| false => String

def f (b : Bool) : chooseType b :=
match b with
| false => ""
| true => (0 : Nat)

#check f
#check (chooseType false)

-- 4
inductive Vec (α : Type u) : Nat → Type u where
  | nil  : Vec α 0
  | cons {n} :  α → Vec α n → Vec α (n + 1)

#check Vec.nil
#check Vec Nat 0
#check Vec Type 0
#check Nat
#check Vec.cons Nat (Vec.nil)

def Vec.default (n : Nat) : Σ (n:Nat), Vec Nat n := match n with
  | 0 => Sigma.mk 0 Vec.nil
  | n+1 => let v := (Vec.default n)
           Sigma.mk (v.fst+1) (v.snd.cons 0)

def forget : (Σ (n : Nat), Vec Nat n) → List Nat
  | ⟨0, Vec.nil⟩ => []
  | ⟨k+1, Vec.cons a b⟩ => a :: forget ⟨k, b⟩

#check Vec.default 3 --- (n : ℕ) × Vec ℕ n
#check Vec.default 0
#check Vec.cons (Vec.nil) 2

-- 5
#check List.recOn

def len {α} (L : List α) : Nat :=
  List.recOn L Nat.zero (fun _h _t mt => mt.succ)

#eval len [0]
#eval len [0, 1]
#eval len [0, 1, 0, 0, 0]
#eval len ([] : List ℕ)



-- 6
namespace Temp
inductive Dyadic where
  | zero    : Dyadic
  | add_one : Dyadic → Dyadic  -- x ↦ x + 1
  | half    : Dyadic → Dyadic  -- x ↦ x / 2
  | neg     : Dyadic → Dyadic  -- x ↦ -x

def Double : Dyadic → Dyadic
  | .zero      => .zero
  | .add_one a => .add_one (.add_one (Double a))
  | .half a    => a
  | .neg a     => .neg (Double a)

def depth : Dyadic → ℕ
  | .zero => 0
  | .add_one a => 1 + depth a
  | .half a => 2 + depth a
  | .neg a => 1 + depth a


def add (a : Dyadic) (b : Dyadic) :=
match a, b with
| .zero, y => y
| .add_one x, y => .add_one (add x y)
| .half x, y => .half (add x (Double y))
| .neg x, y => .neg (add x (.neg y))

def mul (a : Dyadic) (b : Dyadic) :=
  match a, b with
  | .zero, _ => Dyadic.zero
  | .add_one x, y => add y (mul x y)
  | .half x, y => .half (mul x y)
  | .neg x, y => .neg (mul x y)

def to_rat (a : Dyadic) : ℚ :=
  match a with
  | .zero => 0 / 1
  | .add_one x => (to_rat x) + 1
  | .half x => (to_rat x) / 2
  | .neg x => - (to_rat x)

-- Dyadics as defined here are not unique--or rather, `to_rat x` is not unique for all Diadics x. We can see this with something as simple as
#eval to_rat (.zero)
#eval to_rat (.half .zero)
-- `.zero` and `.half .zero` are stored as different values even though they have the same `to_rat`.
end Temp

def sum {α : Type} (f : ℕ → α) (n : ℕ) [hz : Zero α] [ha : Add α] :=
  match n with
  | .zero => hz.zero
  | .succ k => ha.add (f n) (sum f k)



instance : Zero Temp.Dyadic where
  zero := .zero

instance : One Temp.Dyadic where
  one := .add_one .zero


-- 7
instance : Add Temp.Dyadic := ⟨Temp.add⟩

instance : HAdd Temp.Dyadic Temp.Dyadic Temp.Dyadic := ⟨Temp.add⟩

#eval Temp.to_rat (sum (fun n => Temp.Dyadic.half^[n] (Temp.Dyadic.add_one^[n] Temp.Dyadic.zero)) 4)

-- 8
instance : Mul Temp.Dyadic := ⟨Temp.mul⟩
instance : HMul Temp.Dyadic Temp.Dyadic Temp.Dyadic := ⟨Temp.mul⟩

def product {α : Type} (f : ℕ → α) (n : ℕ) [hz : One α] [ha : Mul α] :=
  match n with
  | .zero => hz.one
  | .succ k => ha.mul (f n) (product f k)

#eval Temp.to_rat (product (fun n => Temp.Dyadic.half^[n] (Temp.Dyadic.add_one^[n] Temp.Dyadic.zero)) 4)
end HW_II_4



