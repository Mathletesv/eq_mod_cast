import Mathlib
import Exteq.Tactic

#guard_msgs in
example {C : Nat → Sort*} {a b c : Nat} (x : C (a + b))
    (h₁ : a + b = c) (h₂ : b + a = c) :
    h₁ ▸ x = h₂ ▸ (Nat.add_comm a b ▸ x) := by
  eq_mod_cast

#guard_msgs in
example {a b : ℕ} (x : BitVec (a + b)) :
    BitVec.cast (Nat.add_comm a b) (~~~x) = ~~~(BitVec.cast (Nat.add_comm a b) x) := by
  eq_mod_cast

#guard_msgs in
example {a b : ℕ} (x y : BitVec (a + b)) :
    BitVec.cast (Nat.add_comm a b) (~~~x &&& ~~~y) =
    ~~~(BitVec.cast (Nat.add_comm a b) x) &&& ~~~(BitVec.cast (Nat.add_comm a b) y) := by
  eq_mod_cast

#guard_msgs in
example {α : Type*} {n : ℕ} (hn : 1 ≤ n) (v : Fin (n - 1 + 1) → α) (i : Fin n) :
    (Nat.sub_add_cancel hn ▸ v) i = v (Fin.cast (Nat.sub_add_cancel hn).symm i) := by
  eq_mod_cast

#guard_msgs in
example {α : Type*} {n m k : ℕ} (hn : 1 ≤ n) (v : Nat → Fin (n - 1 + 1) → Nat → α) (i : Fin n) :
    (Nat.sub_add_cancel hn ▸ (v m)) i k = v m (Fin.cast (Nat.sub_add_cancel hn).symm i) k := by
  eq_mod_cast

#guard_msgs in
example {C : Nat → Sort*} {a b c d e : Nat} (g₁ g₂ : Nat → Nat) (f₁ f₂ : Nat → C (a + b))
    (h₁ : a + b = c) (h₃ : f₂ ≍ f₁) (h₄ : g₁ ≍ g₂) :
    h₁ ▸ f₁ (g₁ (e + d) + e) = h₁ ▸ f₂ (g₂ (d + e) + e) := by
  eq_mod_cast [Nat.add_comm e d]

#guard_msgs in
example {C : Nat → Sort*} {a b c d e : Nat} (g₁ g₂ : Nat → Nat) (f₁ f₂ : Nat → C (a + b))
    (h₁ : a + b = c) (h₃ : f₂ ≍ f₁) (h₄ : g₁ ≍ g₂) :
    h₁ ▸ f₁ (g₁ (e + d) + e) = h₁ ▸ f₂ (g₂ (d + e) + e) := by
  eq_mod_cast +omega

#guard_msgs in
example {C : Nat → Sort*} {a b c d e : Nat} (g₁ g₂ : Nat → Nat) (f₁ f₂ : Nat → C (a + b))
    (h₁ : a + b = c) (h₃ : f₂ ≍ f₁) (h₄ : g₁ ≍ g₂) :
    h₁ ▸ f₁ (g₁ (e + d) + e) = h₁ ▸ f₂ (g₂ (d + e) + e) := by
  eq_mod_cast 4
  simp
  omega

/--
warning: Variable name `h₁` is not explicitly referenced.

The binding can be removed (if unused) or named `_` (if used implicitly).

Note: This linter can be disabled with `set_option linter.unusedVariables false`
-/
#guard_msgs in
example {α : Sort*} (f : α → α) (x a : α → (α → α)) (y z b c : α) (h₁ : x y = a b)
  (h₂ : (x y) z = (a b) c) : f ((x y) z) = f ((a b) c) := by
  eq_mod_cast

#guard_msgs in
example (n m : Nat) (eq : n = m) (x : Fin n) (β : Fin m → Type) (f : (x : Fin m) → β x) :
    Eq.rec (α := Type) (motive := fun α _ => α)
      (f (Eq.rec (α := Type) (motive := fun α _ => α) x (congrArg Fin eq)))
      (by cases eq; rfl) =
    f (Eq.rec (α := Nat) (motive := fun n _ => Fin n) x eq) := by
  eq_mod_cast
