-- <vc-preamble>
def find_max_beauty (n: Nat) (tones: List Nat) : Nat := sorry

def countOccurrences (x : Nat) (xs : List Nat) : Nat :=
  xs.foldl (fun count y => if x = y then count + 1 else count) 0
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def unique (xs : List Nat) : List Nat :=
  xs.foldl (fun acc x => if x ∈ acc then acc else x::acc) []
-- </vc-definitions>

-- <vc-theorems>
theorem find_max_beauty_is_min_frequency 
  (tones: List Nat) (h: ∀ x ∈ tones, 1 ≤ x ∧ x ≤ 8) :
  let distinct := unique tones;
  if distinct.length = 8 then
    find_max_beauty tones.length tones = 
      (List.map (fun x => countOccurrences x tones) distinct).minimum?
  else
    find_max_beauty tones.length tones = 0 := sorry

theorem find_max_beauty_non_negative 
  (tones: List Nat) (h: ∀ x ∈ tones, 1 ≤ x ∧ x ≤ 8) :
  find_max_beauty tones.length tones ≥ 0 := sorry

/-
info: 1
-/
-- #guard_msgs in
-- #eval find_max_beauty 8 [1, 2, 3, 4, 5, 6, 7, 8]

/-
info: 2
-/
-- #guard_msgs in
-- #eval find_max_beauty 16 [1, 2, 1, 2, 3, 3, 4, 4, 5, 5, 6, 6, 7, 8, 7, 8]

/-
info: 0
-/
-- #guard_msgs in
-- #eval find_max_beauty 4 [1, 2, 3, 4]
-- </vc-theorems>