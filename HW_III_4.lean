namespace HW_III_4

inductive Person where | mary | steve | ed | jolin

open Person

def on_right (p q : Person) : Prop := match p with
  | mary => q = steve
  | steve => q = ed
  | ed => q = jolin
  | jolin => q = mary

-- 1
def on_left (p q : Person) : Prop := match p with
  | mary => q = jolin
  | jolin => q = ed
  | ed => q = steve
  | steve => q = mary

def on_left' (p q : Person) : Prop := ∃ (a : Person), ∃ (b : Person), on_left p a ∧ on_left a b ∧ on_left b q
def on_left'' (p q : Person) : Prop := on_right q p


-- 2
example : on_left mary jolin :=
  Eq.refl jolin

example : on_left'' mary jolin :=
  rfl


-- 3
variable (α : Type) (P Q : α → Prop)
example : (∀ x, P x → Q x) → (∀ x, P x) → (∀ x, Q x) :=
  fun a b c => (a c) (b c)

-- 4
example : ∃ x, on_right mary x := ⟨steve, rfl⟩
example : ∃ x, ¬on_right mary x := ⟨mary, Person.noConfusion⟩

-- 5
example : (∀ x, P x → r) ↔ (∃ x, P x) → r := ⟨fun a b => Exists.elim b a, fun a b c => a (Exists.intro b c)⟩
example : (∃ x, P x ∨ Q x) ↔ (∃ x, P x) ∨ (∃ x, Q x) :=
  ⟨
    fun a => Exists.elim a (fun b c => Or.elim c (fun d => Or.intro_left (∃ x, Q x) (Exists.intro b d)) (fun e => Or.elim c (fun f => Or.intro_right (∃ x, P x) (Exists.intro b e)) (fun _ => Or.intro_right (∃ x, P x) (Exists.intro b e)))),
    fun a => Or.elim a (fun b => Exists.elim b (fun c d => Exists.intro c (Or.intro_left (Q c) d))) (fun b => Exists.elim b (fun c d => Exists.intro c (Or.intro_right (P c) d)))
  ⟩

-- 6
example : (∀ x, P x → r) ↔ (∃ x, P x) → r :=
  ⟨
    fun a b => Exists.elim b a,
    fun a b c => a ⟨b, c⟩
  ⟩

example : (∃ x, P x ∨ Q x) ↔ (∃ x, P x) ∨ (∃ x, Q x) :=
  ⟨
    fun a => Exists.elim a (fun b c => Or.elim c (fun d => Or.intro_left (∃ x, Q x) (Exists.intro b d)) (fun e => Or.elim c (fun f => Or.intro_right (∃ x, P x) (Exists.intro b e)) (fun _ => Or.intro_right (∃ x, P x) (Exists.intro b e)))),
    fun a => Or.elim a (fun b => Exists.elim b (fun c d => Exists.intro c (Or.intro_left (Q c) d))) (fun b => Exists.elim b (fun c d => Exists.intro c (Or.intro_right (P c) d)))
  ⟩


end HW_III_4
