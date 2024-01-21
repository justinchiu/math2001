/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic
import AutograderLib

math2001_init

namespace Int

/-! # Homework 3

Don't forget to compare with the text version,
https://hrmacbeth.github.io/math2001/Homework.html#homework-3
for clearer statements and any special instructions. -/


@[autograded 4]
theorem problem1 : ∃ x : ℝ, x < 0 ∧ x ^ 2 < 1 := by
  use -0.5
  constructor <;> numbers

@[autograded 5]
theorem problem2 (x : ℚ) : ∃ y : ℚ, y ^ 2 > x := by
  use x+1
  have h := lt_or_ge x 0
  obtain hx | hx := h
  -- x < 0
  · calc
      x < 0 := by rel [hx]
      _ ≤ (x+1)^2 := by extra
  -- x ≥ 0
  · calc
      (x+1)^2 = x^2 + x + 1 + x := by ring
      _ > x := by extra

@[autograded 5]
theorem problem3 {x : ℤ} (hx : Odd x) : Odd (x ^ 3) := by
  dsimp [Odd] at *
  obtain ⟨y, hy⟩ := hx
  use 4 * y^3 + 6 * y^2 + 3 * y
  calc
    x^3 = (2 * y + 1)^3 := by rw [hy]
    _ = 2 * (4 * y^3 + 6 * y^2 + 3 * y) + 1 := by ring

@[autograded 6]
theorem problem4 (n : ℤ) : Odd (5 * n ^ 2 + 3 * n + 7) := by
  dsimp [Odd] at *
  obtain hn | hn := even_or_odd n
  -- Even n
  · obtain ⟨x,hx⟩ := hn
    use 10 * x^2 + 3 * x + 3
    calc
      5*n^2 + 3*n + 7 = 5 * (2*x)^2 + 3*(2*x) + 7 := by rw [hx]
      _ = 2 * (10 * x ^ 2 + 3 * x + 3) + 1 := by ring
  -- Odd n
  · obtain ⟨x,hx⟩ := hn
    use 10 * x^2 + 13 * x + 7
    calc
      5*n^2 + 3*n + 7 = 5 * (2*x+1)^2 + 3*(2*x+1) + 7 := by rw [hx]
      _ = 2 * (10 * x ^ 2 + 13 * x + 7) + 1 := by ring

@[autograded 2]
theorem problem5 : (3 : ℤ) ∣ -9 := by
  sorry

@[autograded 3]
theorem problem6 : ¬(3 : ℤ) ∣ -10 := by
  sorry
