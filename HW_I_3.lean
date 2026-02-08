import Mathlib
-----------------------------------------------------------------------
-- 9
def abs_diff (a b : ℕ) : ℕ :=
  if a ≥ b then a - b else b - a

#eval abs_diff 8 3
#eval abs_diff 3 8

def apply_twice_when_even (f : ℕ → ℕ) (x : ℕ) : ℕ :=
  if Even x then f (f x) else f x

#eval apply_twice_when_even (abs_diff 10) 8
#eval apply_twice_when_even (abs_diff 10) 11

example (a b : ℕ) : abs_diff a b = abs_diff b a := by
  unfold abs_diff
  grind -- it fails without the unfold, interesting



-----------------------------------------------------------------------
-- 18

def fib (x : ℕ) : ℕ := match x with
  | 0 => 1
  | 1 => 1
  -- | k+1 => if x = 1 then 1 else fib k + fib (k - 1)
  | k+1 => fib k + fib (k - 1)

#eval fib 6

def fib_tail (x : ℕ) : ℕ :=
  let rec aux (n a b : ℕ) : ℕ :=
    match n with
    | 0   => a
    | k+1 => aux k b (a + b)
  aux x 1 1

-- 0, 1, 2, 3, 4, 5, 6,  7,  8,  9,  10
-- 1, 1, 2, 3, 5, 8, 13, 21, 34, 55, 89
-----------------------------------------------------------------------
-- 25
def mediant (x y : ℚ) : ℚ :=
  mkRat (x.num + y.num) (x.den + y.den)

def rep (c : Char) (n : ℕ) : String :=
  let rec helper (c: String) (n: ℕ) (sofar: String) : String :=
    match n with
    | 0   => sofar
    | k+1 => helper c k (sofar ++ c)
  helper c.toString n ""

#eval rep 'a' 20

-----------------------------------------------------------------------
-- 31
def le (a : ℕ) (b : ℕ) : Bool :=
  decide (a ≤ b)

#check le

def rev_list {A : Type} (l : List A) : List A :=
  match l with
  | []     => []
  | x :: L => (rev_list L).append [x]

#eval rev_list [0, 1, 2, 3, 4]

def insert_helper {A : Type} (le : (_ _ : A) → Bool) (x : A) : List A → List A
  | [] => [x]
  | y :: ys => if le x y then x :: y :: ys else y :: insert_helper le x ys

def insertionSort {A : Type} (le : (_ _ : A) → Bool) : List A → List A
  | [] => []
  | x :: xs => insert_helper le x (insertionSort le xs)

def str_cmp (a b : String) : Bool := decide (a ≤ b)

#eval insertionSort str_cmp ["Simon", "Chess", "uw", "UW", "7693"]
