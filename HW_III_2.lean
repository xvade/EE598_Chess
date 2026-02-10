namespace HW_III_2
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
end HW_III_2
