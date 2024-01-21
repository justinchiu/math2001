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
  have h := le_or_gt x 0
  obtain hx | hx := h
  -- x ≤ 0
  · have hp : (x+1)^2 > 0 := by sorry
    calc
      (x+1)^2 > 0 := by rel [hp]
      _ ≥ x := by rel [hx]
  -- x > 0
  · have h := le_or_gt x 1
    obtain hxx | hxx := h
    -- x ≤ 1
    · sorry
    -- x > 1
    · sorry

@[autograded 5]
theorem problem3 {x : ℤ} (hx : Odd x) : Odd (x ^ 3) := by
  sorry

@[autograded 6]
theorem problem4 (n : ℤ) : Odd (5 * n ^ 2 + 3 * n + 7) := by
  sorry

@[autograded 2]
theorem problem5 : (3 : ℤ) ∣ -9 := by
  sorry

@[autograded 3]
theorem problem6 : ¬(3 : ℤ) ∣ -10 := by
  sorry
