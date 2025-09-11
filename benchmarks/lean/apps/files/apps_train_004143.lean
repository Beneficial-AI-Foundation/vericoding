-- <vc-preamble>
def indices (n d : Nat) : List (List (List Nat)) := sorry

def sumIndices (idx : List (List Nat)) : Nat := sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def starsAndBars (n k : Nat) : Nat := sorry

theorem indices_valid (n d : Nat) (h1: 0 < n) (h2: n ≤ 10) (h3: d ≤ 10) :
  ∀ idx, idx ∈ indices n d →
    idx.length = 1 ∧
    idx.head!.length = n ∧ 
    (∀ x, x ∈ idx.head! → x ≤ d) ∧
    sumIndices idx = d := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem indices_unique (n d : Nat) (h1: 0 < n) (h2: n ≤ 10) (h3: d ≤ 10) :
  ∀ i j, i ∈ indices n d → j ∈ indices n d → i ≠ j → i.head! ≠ j.head! := sorry

theorem indices_zero (n : Nat) (h1: 0 < n) (h2: n ≤ 10) :
  indices n 0 = [List.replicate 1 (List.replicate n 0)] := sorry

theorem indices_singleton (d : Nat) (h: d ≤ 10) :
  indices 1 d = [[[d]]] := sorry

theorem indices_count (n d : Nat) (h1: 0 < n) (h2: n ≤ 5) (h3: d ≤ 5) :
  (indices n d).length = starsAndBars n d := sorry

/-
info: 6
-/
-- #guard_msgs in
-- #eval len indices(3, 2)

/-
info: 3
-/
-- #guard_msgs in
-- #eval len idx[0]

/-
info: 2
-/
-- #guard_msgs in
-- #eval sum idx[0]
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: unguarded