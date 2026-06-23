import Exteq.Tactic
import Mathlib

set_option trace.debug true

example {α : Sort*} {a b : ℕ} (g : Fin (a + b) → α) (i : Fin (b + a)) :
    (g ∘ Fin.cast (Nat.add_comm b a)) i = g (Fin.cast (Nat.add_comm b a) i) := by
  eq_mod_cast

example {α : Sort*} {a b : ℕ} (f : α → α) (g : Fin (a + b) → α) :
    (f ∘ g) ∘ Fin.cast (Nat.add_comm b a) = f ∘ (g ∘ Fin.cast (Nat.add_comm b a)) := by
  eq_mod_cast

example {C : Nat → Sort*} {a b c : Nat} (x : C (a + b))
    (h₁ : a + b = c) (h₂ : b + a = c) :
    h₁ ▸ x = h₂ ▸ (Nat.add_comm a b ▸ x) :=
  eq_of_heq ((eqRec_heq _ _).trans ((eqRec_heq _ _).symm.trans (eqRec_heq _ _).symm))

set_option pp.proofs true in
example {C : Nat → Sort*} {a b c : Nat} (x : C (a + b))
    (h₁ : a + b = c) (h₂ : b + a = c) :
    h₁ ▸ x = h₂ ▸ (Nat.add_comm a b ▸ x) := by
  eq_mod_cast

example {C : Nat → Sort*} {a b c : Nat} (x : C (a + b))
    (h₁ : a + b = c) (h₂ : b + a = c) :
    HEq (h₁ ▸ x) (h₂ ▸ (Nat.add_comm a b ▸ x)) := by
  eq_mod_cast

example {C : Nat → Sort*} {a b c : Nat} (x : C (a + b))
    (h₁ : a + b = c) (h₂ : b + a = c) :
    h₁ ▸ (Nat.add_comm b a ▸ (Nat.add_comm b a ▸ (Nat.add_comm a b ▸ (Nat.add_comm a b ▸ x)))) =
    h₂ ▸ (Nat.add_comm b a ▸ (Nat.add_comm b a ▸ (Nat.add_comm a b ▸ x))) := by
  eq_mod_cast

example {C : Nat → Sort*} {a b c : Nat} (x : C (a + b))
    (h₁ : a + b = c) (h₂ : b + a = c) :
    h₁ ▸ (Nat.add_comm b a ▸ (Nat.add_comm b a ▸ (Nat.add_comm a b ▸ (Nat.add_comm a b ▸ x)))) ≍
    h₂ ▸ (Nat.add_comm b a ▸ (Nat.add_comm b a ▸ (Nat.add_comm a b ▸ x))) := by
  eq_mod_cast

-- set_option pp.all true in
example {a b : ℕ} (x : BitVec (a + b)) :
    BitVec.cast (Nat.add_comm a b) (x) = (BitVec.cast (Nat.add_comm a b) x) := by
  eq_mod_cast

example {C : Int → Sort u} {a b c d : Int} (x : C a)
    (h₁ : a = b) (h₂ : b = c) (h₃ : a = d) (h₄ : d = c) :
    h₂ ▸ h₁ ▸ x = h₄ ▸ h₃ ▸ x := by
  eq_mod_cast

example {a b : ℕ} (x : BitVec (a + b)) :
    BitVec.cast (Nat.add_comm a b) (~~~x) = ~~~(BitVec.cast (Nat.add_comm a b) x) := by
  eq_mod_cast

example {a b : ℕ} (x y : BitVec (a + b)) :
    BitVec.cast (Nat.add_comm a b) (~~~x &&& ~~~y) =
    ~~~(BitVec.cast (Nat.add_comm a b) x) &&& ~~~(BitVec.cast (Nat.add_comm a b) y) := by
  eq_mod_cast

set_option pp.proofs true in
example {α : Type*} {n : ℕ} (hn : 1 ≤ n) (v : Fin (n - 1 + 1) → α) (i : Fin n) :
    (Nat.sub_add_cancel hn) ▸ v ≍ v := by
  eq_mod_cast

example {α : Type*} {n : ℕ} (hn : 1 ≤ n) (v : Fin (n - 1 + 1) → α) (i : Fin n) :
    i ≍ (Fin.cast (Nat.sub_add_cancel hn).symm i) := by
  eq_mod_cast


example {α : Type*} {n : ℕ} (hn : 1 ≤ n) (v : Fin (n - 1 + 1) → α) (i : Fin n) :
    (Nat.sub_add_cancel hn ▸ v) i = (Nat.sub_add_cancel hn ▸ v) i := by
  eq_mod_cast

set_option pp.all true in
-- v i is not a valid expression, so simply reducing to core will necessarily fail
example {α : Type*} {n : ℕ} (hn : 1 ≤ n) (v : Fin (n - 1 + 1) → α) (i : Fin n) :
    (Nat.sub_add_cancel hn ▸ v) i = v (Fin.cast (Nat.sub_add_cancel hn).symm i) := by
  eq_mod_cast

example {α : Type*} {n m : ℕ} (hn : 1 ≤ n) (v : Nat → Fin (n - 1 + 1) → α) (i : Fin n) :
    (Nat.sub_add_cancel hn ▸ (v m)) i = v m (Fin.cast (Nat.sub_add_cancel hn).symm i) := by
  eq_mod_cast

example {α : Type*} {n m k : ℕ} (hn : 1 ≤ n) (v : Nat → Fin (n - 1 + 1) → Nat → α) (i : Fin n) :
    (Nat.sub_add_cancel hn ▸ (v m)) i k = v m (Fin.cast (Nat.sub_add_cancel hn).symm i) k := by
  eq_mod_cast

example {α : Type*} {n k : ℕ} (hn : 1 ≤ n) (v : Fin (n - 1 + 1) → Nat → α) (i : Fin n) :
    (Nat.sub_add_cancel hn ▸ v) i k = v (Fin.cast (Nat.sub_add_cancel hn).symm i) k := by
  eq_mod_cast

example {α : Type*} {n m : ℕ} (hn : 1 ≤ n) (v : Nat → Fin (n - 1 + 1) → α) (i : Fin n) :
    (Nat.sub_add_cancel hn ▸ (v m)) i = v m (Fin.cast (Nat.sub_add_cancel hn).symm i) := by
  have cast_heq : ∀ {n m : ℕ} (h : n = m) (j : Fin n), HEq (Fin.cast h j) j := by
    intro n m h j
    subst h
    rfl
  have rec_heq : ∀ {n m : ℕ} (h : n = m) (j : Fin n → α), HEq (h ▸ j) j := by
    intro n m h j
    subst h
    rfl
  have right_inner : HEq (Fin.cast (Nat.sub_add_cancel hn).symm i) i :=
    cast_heq ((Nat.sub_add_cancel hn).symm) i
  have left_inner : HEq (Nat.sub_add_cancel hn ▸ (v m)) (v m) :=
    rec_heq (Nat.sub_add_cancel hn) (v m)
  exact congr_heq left_inner right_inner.symm

example {α : Type*} {n : ℕ} (hn : 1 ≤ n) (v : Fin (n - 1 + 1) → α) (i : Fin n) :
    i ≍ (Fin.cast (Nat.sub_add_cancel hn).symm i) := by
  have cast_heq : ∀ {n m} (h : n = m) (j : Fin n), HEq j (Fin.cast h j) := by
    intro n m h j
    subst h
    rfl
  exact cast_heq ((Nat.sub_add_cancel hn).symm) i

example {α : Type*} {n : ℕ} (hn : 1 ≤ n) (v : Fin (n - 1 + 1) → α) (i : Fin n) :
    (Nat.sub_add_cancel hn ▸ v) i = v (Fin.cast (Nat.sub_add_cancel hn).symm i) := by
  have cast_heq : ∀ {n m : ℕ} (h : n = m) (j : Fin n), HEq (Fin.cast h j) j := by
    intro n m h j
    subst h
    rfl
  have rec_heq : ∀ {n m : ℕ} (h : n = m) (j : Fin n → α), HEq (h ▸ j) j := by
    intro n m h j
    subst h
    rfl
  have right_inner : HEq (Fin.cast (Nat.sub_add_cancel hn).symm i) i :=
    cast_heq ((Nat.sub_add_cancel hn).symm) i
  have left_inner : HEq (Nat.sub_add_cancel hn ▸ v) v :=
    rec_heq (Nat.sub_add_cancel hn) v
  exact congr_heq left_inner right_inner.symm
