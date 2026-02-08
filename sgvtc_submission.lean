
namespace HW_III_2
-- 1

--  Cannot prove (p∨q) ∧ (p∨r) → p ∨ (q∧r) without law of the excluded middle.
-- (p∨q) ∧ (p∨r) → p ∨ (q∧r)


-- 2
/-
Example: ⊢ (p → q) → p → q
Proof: →-Intro
State: p → q ⊢ p → q
Proof: Axiom
-/

-- 3
/-
Example: ⊢ p ∧ q → p ∨ q
→-Intro
State: p ∧ q ⊢ p ∨ q
∨-Intro-Left (p):
State: p ∧ q ⊢ p
∧-Elim-Left
State: Goals accomplished!
-/

-- 4
/-
Example: ⊢ p ∨ (q∧r) → (p∨q) ∧ (p∨r)
→-Intro
State: p ∨ (q∧r) ⊢ (p∨q) ∧ (p∨r)
∧-Intro
State 1: p ∨ (q∧r) ⊢ p∨q
State 2: p ∨ (q∧r) ⊢ p∨r
∨-Elim (State 1) with φ=p and ψ=q∧r:
State 1a: p ∨ (q∧r) ⊢ p ∨ (q∧r)
State 1b: p ∨ (q∧r) ⊢ p → p ∨ q
State 1c: p ∨ (q∧r) ⊢ q∧r → p ∨ q
State 2: p ∨ (q∧r) ⊢ p∨r
Axiom (State 1a)
State 1b: p ∨ (q∧r) ⊢ p → p ∨ q
State 1c: p ∨ (q∧r) ⊢ q∧r → p ∨ q
State 2: p ∨ (q∧r) ⊢ p∨r
→-Intro (State 1b)
State 1b: p ∨ (q∧r), p ⊢ p ∨ q
State 1c: p ∨ (q∧r) ⊢ q∧r → p ∨ q
State 2: p ∨ (q∧r) ⊢ p∨r
→-Intro (State 1c)
State 1b: p ∨ (q∧r), p ⊢ p ∨ q
State 1c: p ∨ (q∧r), q∧r ⊢ p ∨ q
State 2: p ∨ (q∧r) ⊢ p∨r
∨-Intro-Left (State 1b)
State 1b: p ∨ (q∧r), p ⊢ p
State 1c: p ∨ (q∧r), q∧r ⊢ p ∨ q
State 2: p ∨ (q∧r) ⊢ p∨r
Axiom (State 1b)
State 1c: p ∨ (q∧r), q∧r ⊢ p ∨ q
State 2: p ∨ (q∧r) ⊢ p∨r
∨-Intro-Right (State 1c)
State 1c: p ∨ (q∧r), q∧r ⊢ q
State 2: p ∨ (q∧r) ⊢ p∨r
∧-Elim-Left (State 1c)
State 1c: p ∨ (q∧r), q∧r ⊢ q∧r
State 2: p ∨ (q∧r) ⊢ p∨r
Axiom (State 1c)
State: p ∨ (q∧r) ⊢ p∨r
∨-Elim with φ=p and ψ=q∧r:
State 1: p ∨ (q∧r) ⊢ p ∨ (q∧r)
State 2: p ∨ (q∧r) ⊢ p → p ∨ r
State 3: p ∨ (q∧r) ⊢ q∧r → p ∨ r
→-Intro (State 2)
State 1: p ∨ (q∧r) ⊢ p ∨ (q∧r)
State 2: p ∨ (q∧r), p ⊢ p ∨ r
State 3: p ∨ (q∧r) ⊢ q∧r → p ∨ r
→-Intro (State 3)
State 1: p ∨ (q∧r) ⊢ p ∨ (q∧r)
State 2: p ∨ (q∧r), p ⊢ p ∨ r
State 3: p ∨ (q∧r), q∧r ⊢ p ∨ r
Axiom (State 1)
State 2: p ∨ (q∧r), p ⊢ p ∨ r
State 3: p ∨ (q∧r), q∧r ⊢ p ∨ r
∨-Intro-Left (State 2)
State 2: p ∨ (q∧r), p ⊢ p
State 3: p ∨ (q∧r), q∧r ⊢ p ∨ r
Axiom (State 2)
State: p ∨ (q∧r), q∧r ⊢ p ∨ r
∨-Intro-Right
State: p ∨ (q∧r), q∧r ⊢ r
∧-Elim-Right
State: p ∨ (q∧r), q∧r ⊢ q∧r
Axiom
State: Goals accomplished!


The inverse direction is not provable without classical logic.
-/

-- 5
/-
Example: ⊢ ¬¬p → p ∧ p → ¬¬p
∧-Intro
State 1: ⊢ ¬¬p → p
State 2: ⊢ p → ¬¬p
→-Intro (State 1)
State 1: ¬¬p ⊢ p
State 2: ⊢ p → ¬¬p
→-Intro (State 2)
State 1: ¬¬p ⊢ p
State 2: p ⊢ ¬¬p
→-Intro (State 2)
State 1: ¬¬p ⊢ p
State 2: p, ¬p ⊢ False
→-Elim (State 2)
State 1: ¬¬p ⊢ p
State 2a: p, ¬p ⊢ p
State 2b: p, ¬p ⊢ ¬p
Axiom (State 2a)
State 1: ¬¬p ⊢ p
State 2: p, ¬p ⊢ ¬p
Axiom (State 2)
State: ¬¬p ⊢ p          -- (p → False) → False
Law of the Excluded Middle
State: ¬¬p, p ∨ ¬p ⊢ p
∨-Elim
State 1: ¬¬p, p ∨ ¬p ⊢ p ∨ ¬p
State 2: ¬¬p, p ∨ ¬p ⊢ p → p
State 3: ¬¬p, p ∨ ¬p ⊢ ¬p → p
Axiom (State 1)
State 2: ¬¬p, p ∨ ¬p ⊢ p → p
State 3: ¬¬p, p ∨ ¬p ⊢ ¬p → p
→-Intro (State 2)
State 2: ¬¬p, p ∨ ¬p, p ⊢ p
State 3: ¬¬p, p ∨ ¬p ⊢ ¬p → p
Axiom (State 2)
State: ¬¬p, p ∨ ¬p ⊢ ¬p → p
→-Intro
State: ¬¬p, p ∨ ¬p, ¬p ⊢ p
→-Elim
State 1: ¬¬p, p ∨ ¬p, ¬p ⊢ False → p
State 2: ¬¬p, p ∨ ¬p, ¬p ⊢ False
→-Intro (State 1)
State 1: ¬¬p, p ∨ ¬p, ¬p, False ⊢ p
State 2: ¬¬p, p ∨ ¬p, ¬p ⊢ False
Exfalso (State 1)
State 1: ¬¬p, p ∨ ¬p, ¬p, False ⊢ False
State 2: ¬¬p, p ∨ ¬p, ¬p ⊢ False
Axiom (State 1)
State: ¬¬p, p ∨ ¬p, ¬p ⊢ False
→-Elim
State 1: ¬¬p, p ∨ ¬p, ¬p ⊢ ¬¬p
State 2: ¬¬p, p ∨ ¬p, ¬p ⊢ ¬p
Axiom (State 1)
State: ¬¬p, p ∨ ¬p, ¬p ⊢ ¬p
Axiom
State: Goals accomplished!
-/
end HW_III_2


namespace HW_III_3
-- 1
variable (P Q : Prop)

example : P → P → P → P :=
  fun a _ _ => a


example : (P → Q) → (¬Q → ¬P) :=
  fun h1 => (fun h2 => (fun h3 => h2 (h1 h3)))


example : ¬P → (P → Q) :=
  fun hnp => fun hp => nomatch (hnp hp)


example : (∀ x, x > 0) → (∀ y, y > 0) :=
  fun a => a
end HW_III_3
