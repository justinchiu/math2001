/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic
import AutograderLib

math2001_init

/-! # Homework 1

Don't forget to compare with the text version,
https://hrmacbeth.github.io/math2001/Homework.html#homework-1
for clearer statements and any special instructions. -/


@[autograded 5]
theorem problem1 {p q : ℤ} (h1 : p + 4 * q = 1) (h2 : q - 1 = 2) : p = -11 := by
  calc
    p = p + 4 * q - 4 * q := by ring
    _ = 1 - 4 * q := by rw [h1]
    _ = 1 - 4 * (q - 1 + 1) := by ring
    _ = 1 - 4 * (2 + 1) := by rw [h2]
    _ = -11 := by ring

@[autograded 5]
theorem problem2 {a b : ℝ} (h1 : a + 2 * b = 4) (h2 : a - b = 1) : a = 2 := by
  calc
    a = (a + 2 * b + 2 * (a-b)) / 3 := by ring
    _ = (4 + 2 * 1) / 3 := by rw [h1, h2]
    _ = 2 := by ring

@[autograded 5]
theorem problem3 {x : ℤ} (hx : x ≥ 9) : x ^ 3 - 8 * x ^ 2 + 2 * x ≥ 3 := by
  calc
    x ^ 3 - 8 * x ^ 2 + 2 * x = x * x * x - 8 * x * x + 2 * x := by ring
    _ ≥ 9 * x * x - 8 * x * x + 2 * 9 := by rel [hx]
    _ = x ^ 2 + 18 := by ring
    _ ≥ 9 ^ 2 + 18 := by rel [hx]
    _ ≥ 3 := by numbers

@[autograded 5]
theorem problem4 {x : ℚ} : x ^ 2 - 2 * x ≥ -1 := by
  calc
    x^2 - 2*x = x^2-2*x+1-1 := by ring
    _ = (x-1)^2-1 := by ring
    _ ≥ -1 := by extra

@[autograded 5]
theorem problem5 (a b : ℝ) (h1 : -b ≤ a) (h2 : a ≤ b) : a ^ 2 ≤ b ^ 2 := by
  have hp : 0 ≤ a+b := by
    calc
      0 = (-b) + b := by ring
      _ ≤ a + b := by rel [h1]
  have hm : a-b ≤ 0 := by
    calc
      a-b ≤  a - a := by rel [h2]
      _ = 0 := by ring
  have h : (a+b)*(a-b) ≤ 0 := by
    sorry
  calc
    a^2 = a^2 - b^2 + b^2 := by ring
    _ = (a+b)*(a-b) + b^2 := by ring
    _ ≤ 0 + b^2 := by rel [h]
    _ = b^2 := by ring
