import Mathlib
-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- no helpers needed
-- </vc-helpers>

-- <vc-definitions>
def UpdateElements (a : Array Int) : Array Int :=
if hsz : 8 ≤ a.size then
  Array.ofFn (fun (i : Fin a.size) =>
    if h7 : (i.1 = 7) then (516 : Int)
    else if h4 : (i.1 = 4) then a[i] + 3
    else a[i])
else
  a
-- </vc-definitions>

-- <vc-theorems>
theorem UpdateElements_spec (a : Array Int) :
a.size ≥ 8 →
let a' := UpdateElements a
(a'[4]! = a[4]! + 3) ∧
(a'[7]! = 516) ∧
(∀ i, 0 ≤ i ∧ i < a.size → i ≠ 7 ∧ i ≠ 4 → a'[i]! = a[i]!) :=
by
  intro hsz
  have h4lt : 4 < a.size := Nat.lt_of_lt_of_le (by decide) hsz
  have h7lt : 7 < a.size := Nat.lt_of_lt_of_le (by decide) hsz
  have h44 : 4 = 4 := rfl
  have h47 : 4 ≠ 7 := by decide
  have h77 : 7 = 7 := rfl
  have h74 : 7 ≠ 4 := by decide
  constructor
  ·
    have : (let a' := UpdateElements a; a'[4]!) = a[4]! + 3 := by
      simp [UpdateElements, hsz, Array.get!, h4lt, h47, h44]
    simpa using this
  ·
    constructor
    ·
      have : (let a' := UpdateElements a; a'[7]!) = 516 := by
        simp [UpdateElements, hsz, Array.get!, h7lt, h77, h74]
      simpa using this
    ·
      intro i hi hneq
      have hi_lt : i < a.size := hi.2
      have h7ne : (⟨i, hi_lt⟩ : Fin a.size).1 ≠ 7 := by simpa using hneq.1
      have h4ne : (⟨i, hi_lt⟩ : Fin a.size).1 ≠ 4 := by simpa using hneq.2
      have : (let a' := UpdateElements a; a'[i]!) = a[i]! := by
        simp [UpdateElements, hsz, Array.get!, hi_lt, h7ne, h4ne]
      simpa using this
-- </vc-theorems>
