import Mathlib
set_option linter.style.longLine false

-- 1
variable (a : Type → Type)
variable (b : Type)

#check fun (c : Type) (_ : Type) => c
#check fun (_ : Type → Type) => Prop

-- 2
def prepend_label : String → String := String.append "STRING: "

#eval prepend_label "hi"
#eval prepend_label "simon"
#check prepend_label

-- 3
namespace Temp
variable (a : A) (b : B) (f : A → B)
#check f a
end Temp

-- 4
variable (x : A)
#reduce (types:=true) (fun a => x) x

def M : A → A → A → A → A := fun a b c d => x
#reduce M x x x x x -- should have size of 5

-- 5
def α := Type
def N := ∀ {α}, (α → α) → α → α
def c₀ := fun {α} ( f : α → α ) => fun ( x : α ) => x
def c₁ := fun {α} ( f : α → α ) => fun x => f x
def c₂ := fun {α} ( f : α → α ) => fun x => f (f x)
def c₃ := fun {α} ( f : α → α ) => fun x => f (f (f x))
def c₄ := fun {α} ( f : α → α ) => fun x => f (f (f (f x)))
def c₅ := fun {α} ( f : α → α ) => fun x => f (f (f (f (f x))))
def c₆ := fun {α} ( f : α → α ) => fun x => f (f (f (f (f (f x)))))

def mul := fun (m n : N) (f : α → α) (x : α) => m (n f) x

def double := mul c₂

def succ := fun (n : N) (f : α → α) x => f (n f x)

#check N
#reduce (types:=true) double c₀   -- 0
#reduce (types:=true) double c₃   -- 6

-- 6
#check_failure fun x y => x y
#check_failure fun x y z => x y z
#check_failure fun x y => y (y (y x))
#check_failure fun x y z => (y x) z

#check fun (x : Type → Type) y => x y
#check fun (x : Type → Type → Type) y z => x y z
#check fun x (y : Type → Type) => y (y (y x))
#check fun x (y : Type → Type → Type) z => (y x) z

-- 7
#check c₀
#check c₁
def I.{u} : Type u → Type u := fun x => x

#reduce (types:=true) c₀
#reduce (types:=true) c₁
#reduce (types:=true) c₂


def pred := fun (n : N) (f : α → α) (x : α) => n (fun r i => i (r f)) (fun _ => x) (fun u => u)
#reduce (types:=true) pred c₀


#check pred c₀
#check pred c₁
#reduce (types:=true) pred c₀
#reduce (types:=true) pred c₁
#reduce (types:=true) pred c₂
