import Exteq.Tactic

example {C : Nat → Sort*} {a b c d : Nat} (f : Nat → C (a + b)) (g : Nat → C (a + b))
    (h₁ : a + b = c) (h₃ : f ≍ g) :
    h₁ ▸ (f d) = h₁ ▸ (g d) := by
  eq_mod_cast [h₃]

-- f ((x y) z) = f ((a b) c) <— goal
-- x y = a b
-- (x y) z = (a b) c

example {α : Sort*} (f : α → α) (x a : α → (α → α)) (y z b c : α) (h₁ : x y = a b)
  (h₂ : (x y) z = (a b) c) : f ((x y) z) = f ((a b) c) := by
  eq_mod_cast [h₁, h₂] -- it does match outer equalities when possible

example {C : Nat → Sort*} {a b c d e : Nat} (f : Nat → C (a + b)) (g : Nat → C (a + b))
    (h₁ : a + b = c) (h₃ : f ≍ g) :
    h₁ ▸ (f (d + e)) = h₁ ▸ (g (e + d)) := by
  eq_mod_cast [h₃, Nat.add_comm d e]

-- example of creating a hole
example {C : Nat → Sort*} {a b c d e : Nat} (f : Nat → C (a + b)) (g : Nat → C (a + b))
    (h₁ : a + b = c) (h₃ : f ≍ g) :
    h₁ ▸ (f (d + e)) = h₁ ▸ (g (e + d)) := by
  eq_mod_cast [Nat.add_comm d e]
  exact h₃

example {C : Nat → Sort*} {a b c d e : Nat} (f : Nat → C (a + b)) (g : Nat → C (a + b))
    (h₁ : a + b = c) (h₃ : f ≍ g) :
    h₁ ▸ ((fun n => f n) (d + e)) = h₁ ▸ ((fun n => (fun x => g x) n) (e + d)) := by
  eq_mod_cast [h₃, Nat.add_comm d e]



/--
warning: Please, write a comment here or remove this line, but do not place empty lines within commands!
Context:
                                                                ↓
  ⏎    h₁ ▸ f₁ (g₁ (e + d) + e) = h₁ ▸ f₂ (g₂ (d + e) + e) := by⏎⏎  eq_mod_cast [h₃, Nat.add_comm e d, h₄]⏎⏎

Note: This linter can be disabled with `set_option linter.style.emptyLine false`
-/
#guard_msgs in
example {C : Nat → Sort*} {a b c d e : Nat} (g₁ g₂ : Nat → Nat) (f₁ f₂ : Nat → C (a + b))
    (h₁ : a + b = c) (h₃ : f₁ ≍ f₂) (h₄ : g₁ ≍ g₂) :
    h₁ ▸ f₁ (g₁ (e + d) + e) = h₁ ▸ f₂ (g₂ (d + e) + e) := by

  eq_mod_cast [h₃, Nat.add_comm e d, h₄]

/--

-/
#guard_msgs in
example {C : Nat → Sort*} {a b c d e : Nat} (g₁ g₂ : Nat → Nat) (f₁ f₂ : Nat → C (a + b))
    (h₁ : a + b = c) (h₃ : f₁ ≍ f₂) (h₄ : g₁ ≍ g₂) :
    h₁ ▸ f₁ (g₁ (e + d) + e) = h₁ ▸ f₂ (g₂ (d + e) + e) := by
  eq_mod_cast [h₄, Nat.add_comm e d]
  exact h₃

example {C : Nat → Sort*} {a b c d e : Nat} (g₁ g₂ : Nat → Nat) (f₁ f₂ : Nat → C (a + b))
    (h₁ : a + b = c) (h₃ : f₁ ≍ f₂) (h₄ : g₁ ≍ g₂) :
    h₁ ▸ f₁ (g₁ (e + d) + e) = h₁ ▸ f₂ (g₂ (d + e) + e) := by
  eq_mod_cast [Nat.add_comm e d]
  exact h₃
  exact h₄

example {C : Nat → Sort*} {a b c d e : Nat} (g₁ g₂ : Nat → Nat) (f₁ f₂ : Nat → C (a + b))
    (h₁ : a + b = c) (h₃ : f₁ ≍ f₂) (h₄ : g₁ ≍ g₂) :
    h₁ ▸ f₁ (g₁ (e + d) + e) = h₁ ▸ f₂ (g₂ (d + e) + e) := by
  eq_mod_cast 4
  exact h₃
  exact h₄
  exact heq_of_eq (Nat.add_comm e d)

example {C : Nat → Sort*} {a b c d e : Nat} (g₁ g₂ : Nat → Nat) (f₁ f₂ : Nat → C (a + b))
    (h₁ : a + b = c) (h₃ : f₁ ≍ f₂) (h₄ : g₁ ≍ g₂) :
    h₁ ▸ f₁ (g₁ (e + d) + e) = h₁ ▸ f₂ (g₂ (d + e) + e) := by
  eq_mod_cast 4 [h₃]
  exact h₄
  exact heq_of_eq (Nat.add_comm e d)
