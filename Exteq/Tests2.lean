import Exteq.Tactic

variable (n m : Nat) (eq : n = m) (x : Fin n)

set_option trace.debug true

example (β : (n : Nat) → Fin n → Type) (f : (n : Nat) → (x : Fin n) → β n x) :
    Eq.rec (α := Type) (motive := fun α _ => α) (f n x) (by cases eq; rfl) = f m (eq ▸ x) := by
  eq_mod_cast

set_option pp.all true in
-- Simplest example where rfl doesn't suffice
example (f : Fin m → Nat) :
    f (Eq.rec (α := Type) (motive := fun α _ => α) x (congrArg Fin eq)) =
    f (Eq.rec (α := Nat) (motive := fun n _ => Fin n) x eq) := by
  -- rfl -- fails
  eq_mod_cast

example :
    Eq.rec (α := Type) (motive := fun α _ => α) x (congrArg Fin eq) =
    Eq.rec (α := Nat) (motive := fun n _ => Fin n) x eq := by
  -- rfl -- fails
  eq_mod_cast

-- Dependent family
example (β : Fin m → Type) (f : (x : Fin m) → β x) :
    Eq.rec (α := Type) (motive := fun α _ => α)
      (f (Eq.rec (α := Type) (motive := fun α _ => α) x (congrArg Fin eq)))
      (by cases eq; rfl) =
    f (Eq.rec (α := Nat) (motive := fun n _ => Fin n) x eq) := by
  eq_mod_cast


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

example {C : Nat → Sort*} {a b c d e : Nat} (f : Nat → C (a + b)) (g : Nat → C (a + b))
    (h₁ : a + b = c) (h₃ : f ≍ g) :
    h₁ ▸ ((fun n => f n) (d + e)) = h₁ ▸ ((fun n => (fun x => g x) n) (e + d)) := by
  eq_mod_cast [h₃, Nat.add_comm d e]


example {C : Nat → Sort*} {a b c d e : Nat} (g₁ g₂ : Nat → Nat) (f₁ f₂ : Nat → C (a + b))
    (h₁ : a + b = c) (h₃ : f₁ ≍ f₂) (h₄ : g₁ ≍ g₂) :
    h₁ ▸ f₁ (g₁ (e + d) + e) = h₁ ▸ f₂ (g₂ (d + e) + e) := by
  eq_mod_cast [h₃, Nat.add_comm e d, h₄]

example {C : Nat → Sort*} {a b c d e : Nat} (g₁ g₂ : Nat → Nat) (f₁ f₂ : Nat → C (a + b))
    (h₁ : a + b = c) (h₃ : f₁ ≍ f₂) (h₄ : g₁ ≍ g₂) :
    h₁ ▸ f₁ (g₁ (e + d) + e) = h₁ ▸ f₂ (g₂ (d + e) + e) := by
  eq_mod_cast +omega

example {C : Nat → Sort*} {a b c d e : Nat} (g₁ g₂ : Nat → Nat) (f₁ f₂ : Nat → C (a + b))
    (h₁ : a + b = c) (h₃ : f₁ ≍ f₂) (h₄ : g₁ ≍ g₂) :
    h₁ ▸ f₁ (g₁ (e + d) + e) = h₁ ▸ f₂ (g₂ (d + e) + e) := by
  eq_mod_cast 4
  exact heq_of_eq (Nat.add_comm e d)
