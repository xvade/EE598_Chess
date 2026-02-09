namespace HW_III_3
variable (p q r : Prop)

-- 1
example : p ∧ (q ∧ r) → (p ∧ q) ∧ r :=
  fun ⟨hp, hq, hr⟩ => ⟨⟨hp, hq⟩, hr⟩


-- 2
example (p q : Prop) : (p ↔ q) ↔ (p → q) ∧ (q → p) :=
  Iff.intro
    (fun hpiffq => ⟨hpiffq.mp, hpiffq.mpr⟩)
    (fun hmp_and_mpr => ⟨hmp_and_mpr.left, hmp_and_mpr.right⟩)

-- 3
example : p ∨ q ↔ q ∨ p := ⟨fun a => Or.elim a Or.inr Or.inl, fun a => Or.elim a Or.inr Or.inl⟩
example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) := ⟨fun a => Or.elim a (fun b => Or.elim b Or.inl (fun c => Or.intro_right p (Or.intro_left r c))) (fun b => Or.intro_right p (Or.intro_right q b)), fun a => (Or.elim a (fun b => Or.intro_left r (Or.intro_left q b)) (fun b => Or.elim b (fun c => Or.intro_left r (Or.intro_right p c)) (fun c => Or.intro_right (p ∨ q) c)))⟩
example : ¬(p ∨ q) ↔ ¬p ∧ ¬q := ⟨fun a => ⟨fun b => a (Or.intro_left q b), fun b => a (Or.intro_right p b)⟩, fun a b => (Or.elim b a.left a.right)⟩
example : ¬(p ∧ ¬p) := fun a => a.right a.left
example : (¬p ∨ q) → (p → q) := fun a b => Or.elim a (fun c => nomatch (c b)) id
example : p ∨ False ↔ p := ⟨fun a => Or.elim a id (fun b => nomatch b), Or.intro_left False⟩
example : p ∧ False ↔ False := ⟨fun a => a.right, fun a => nomatch a⟩

-- 4
example : (p → q) → (¬p ∨ q) := fun a => Or.elim (Classical.em p) (fun b => Or.intro_right (¬p) (a b)) (Or.intro_left q)

-- 5
inductive Nor (p q : Prop) : Prop where
  | intro : ¬p → ¬q → Nor p q

def Nor.elim_left {p q : Prop} (hnpq : Nor p q) : ¬p := match hnpq with
| Nor.intro a _ => a
def Nor.elim_right {p q : Prop} (hnpq : Nor p q) : ¬q := match hnpq with
| Nor.intro _ b => b

-- 6
example : ¬p → (Nor p p) := fun a => Nor.intro a a
example : (Nor p q) → ¬(p ∨ q) := fun a b => Or.elim b a.elim_left a.elim_right
example : ¬(p ∨ q) → (Nor p q) := fun a => Nor.intro (fun b => a (Or.intro_left q b)) (fun b => a (Or.intro_right p b))

end HW_III_3
