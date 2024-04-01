import MIL.Common
import Mathlib.Data.Real.Basic

namespace C03S05

section

variable {x y : ℝ}

example (h : y > x ^ 2) : y > 0 ∨ y < -1 := by
  left
  linarith [pow_two_nonneg x]

example (h : -y > x ^ 2 + 1) : y > 0 ∨ y < -1 := by
  right
  linarith [pow_two_nonneg x]

example (h : y > 0) : y > 0 ∨ y < -1 :=
  Or.inl h

example (h : y < -1) : y > 0 ∨ y < -1 :=
  Or.inr h

example : x < |y| → x < y ∨ x < -y := by
  rcases le_or_gt 0 y with h | h
  · rw [abs_of_nonneg h]
    intro h; left; exact h
  . rw [abs_of_neg h]
    intro h; right; exact h

example : x < |y| → x < y ∨ x < -y := by
  cases le_or_gt 0 y
  case inl h =>
    rw [abs_of_nonneg h]
    intro h; left; exact h
  case inr h =>
    rw [abs_of_neg h]
    intro h; right; exact h

example : x < |y| → x < y ∨ x < -y := by
  cases le_or_gt 0 y
  next h =>
    rw [abs_of_nonneg h]
    intro h; left; exact h
  next h =>
    rw [abs_of_neg h]
    intro h; right; exact h


example : x < |y| → x < y ∨ x < -y := by
  match le_or_gt 0 y with
    | Or.inl h =>
      rw [abs_of_nonneg h]
      intro h; left; exact h
    | Or.inr h =>
      rw [abs_of_neg h]
      intro h; right; exact h

namespace MyAbs

theorem le_abs_self (x : ℝ) : x ≤ |x| := by
  rcases le_or_gt 0 x with h | h
  . rw [abs_of_nonneg h]
  . rw [abs_of_neg h]
    have: -x > 0 := by linarith
    have h1: x < -x := by
      apply lt_trans h this
    linarith[h1]


theorem neg_le_abs_self (x : ℝ) : -x ≤ |x| := by
  rcases le_or_gt 0 x with h | h
  . rw [abs_of_nonneg h]
    have: -x ≤ 0 := by linarith
    apply ge_trans h this
  . rw [abs_of_neg h]

theorem abs_add (x y : ℝ) : |x + y| ≤ |x| + |y| := by
  rcases le_or_gt 0 x with h1 | h2
  rcases le_or_gt 0 y with h3 | h4
  . rw [abs_of_nonneg h1, abs_of_nonneg h3]
    have: x + y ≥ 0:= by
      rw[← add_zero 0]
      apply add_le_add h1 h3
    rw [abs_of_nonneg this]
  . rw[abs_of_nonneg h1, abs_of_neg h4]
    rcases le_or_gt 0 (x+y) with h | h
    rw[abs_of_nonneg h]
    linarith
    rw[abs_of_neg h]
    linarith
  rcases le_or_gt 0 y with h3 | h4
  . rw[abs_of_nonneg h3, abs_of_neg h2]
    rcases le_or_gt 0 (x+y) with h | h
    rw[abs_of_nonneg h]
    linarith
    rw[abs_of_neg h]
    linarith
  . rw[abs_of_neg h4, abs_of_neg h2]
    rcases le_or_gt 0 (x+y) with h | h
    rw[abs_of_nonneg h]
    linarith
    rw[abs_of_neg h]
    linarith


theorem lt_abs : x < |y| ↔ x < y ∨ x < -y := by
  constructor
  . intro h
    rcases le_or_gt 0 y with h' | h'
    . left
      have: |y| = y := by apply abs_of_nonneg h'
      have: y = |y| := by linarith
      rw[this]
      exact h
    . right
      have: |y| = -y := by apply abs_of_neg h'
      rw[← this]
      exact h
  . intro h
    rcases h with h' | h'
    . have: y ≤ |y| := by apply le_abs_self
      linarith
    . have: -y ≤ |y| := by apply neg_le_abs_self
      linarith


theorem abs_lt : |x| < y ↔ -y < x ∧ x < y := by
  constructor
  . rcases le_or_gt 0 x with h | h
    . rw[abs_of_nonneg h]
      intro h'
      constructor
      . linarith
      . exact h'
    . rw[abs_of_neg h]
      intro h'
      constructor
      . linarith
      . linarith
  . rintro ⟨ h1, h2⟩
    rcases le_or_gt 0 x with h | h
    . rw[abs_of_nonneg h]
      exact h2
    . rw[abs_of_neg h]
      linarith

end MyAbs

end

example {x : ℝ} (h : x ≠ 0) : x < 0 ∨ x > 0 := by
  rcases lt_trichotomy x 0 with xlt | xeq | xgt
  · left
    exact xlt
  · contradiction
  . right; exact xgt

example {m n k : ℕ} (h : m ∣ n ∨ m ∣ k) : m ∣ n * k := by
  rcases h with ⟨a, rfl⟩ | ⟨b, rfl⟩
  · rw [mul_assoc]
    apply dvd_mul_right
  . rw [mul_comm, mul_assoc]
    apply dvd_mul_right

example {z : ℝ} (h : ∃ x y, z = x ^ 2 + y ^ 2 ∨ z = x ^ 2 + y ^ 2 + 1) : z ≥ 0 := by
  sorry

example {x : ℝ} (h : x ^ 2 = 1) : x = 1 ∨ x = -1 := by
  sorry

example {x y : ℝ} (h : x ^ 2 = y ^ 2) : x = y ∨ x = -y := by
  sorry

section
variable {R : Type*} [CommRing R] [IsDomain R]
variable (x y : R)

example (h : x ^ 2 = 1) : x = 1 ∨ x = -1 := by
  sorry

example (h : x ^ 2 = y ^ 2) : x = y ∨ x = -y := by
  sorry

end

example (P : Prop) : ¬¬P → P := by
  intro h
  cases em P
  · assumption
  . contradiction

example (P : Prop) : ¬¬P → P := by
  intro h
  by_cases h' : P
  · assumption
  contradiction

example (P Q : Prop) : P → Q ↔ ¬P ∨ Q := by
  sorry
