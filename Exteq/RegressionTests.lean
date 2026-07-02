import Mathlib
import Exteq.Tactic

-- Cast / Rewrite handling

#guard_msgs in
example {C : Nat → Sort*} {a b c : Nat} (x : C (a + b))
    (h₁ : a + b = c) :
    h₁ ▸ x = x := by
  eq_mod_cast

#guard_msgs in
example {C : Nat → Type} {a b : Nat} (h : a = b) (x : C a) :
    (@Eq.recOn Nat a (fun x _ => C x) b h x : C b) ≍ x := by
  eq_mod_cast

#guard_msgs in
example {α β : Type} (h : α = β) (b : β) : Eq.mpr h b ≍ b := by
  eq_mod_cast

#guard_msgs in
example {α β : Type} (h : α = β) (a : α) : Eq.mp h a ≍ a := by
  eq_mod_cast

#guard_msgs in
example {motive : Nat → Prop} {a b : Nat} (h : a = b) (m : motive a) :
    (Eq.subst h m : motive b) ≍ m := by
  eq_mod_cast

#guard_msgs in
example {α β : Type} (h : α = β) (a : α) : cast h a ≍ a := by
  eq_mod_cast

-- Nesting / Function handling

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

variable {n m : Nat} (eq : n = m)

#guard_msgs in
example : (fun (y : Fin n) => y) ≍ (fun (y : Fin m) => y) := by
  eq_mod_cast

#guard_msgs in
example : (fun (lt : 0 < n) => @Fin.mk n 0 (@id (0 < n) lt))
        ≍ (fun (lt : 0 < m) => @Fin.mk m 0 (@id (0 < m) lt)) := by
  eq_mod_cast

#guard_msgs in
example : (∀ (lt : 0 < n), @Eq (Fin n) ⟨0, lt⟩ ⟨0, lt⟩)
        = (∀ (lt : 0 < m), @Eq (Fin m) ⟨0, lt⟩ ⟨0, lt⟩) := by
  eq_mod_cast

#guard_msgs in
example
  (F : Nat → Type) (G : (n : Nat) → F n → Type) (r : (n : Nat) → (f : F n) → G n f → Nat)
  (f : F n) (g : G n f) (g' : G m (eq ▸ f)) (h : g ≍ g') :
  (let a : Nat := n
    let B : Type := G a f
    let c : B := g
    let c' : G m (eq ▸ f) := g'
    r n f c = r m (eq ▸ f) c') := by
  eq_mod_cast

#guard_msgs in
example : Fin (n + n) = Fin (2 * n) := by
  eq_mod_cast +omega

#guard_msgs in
example (f g : (n : Nat) → Fin n → Nat) (h : f ≍ g) (i : Fin n) : f n i = g n i := by
  eq_mod_cast
