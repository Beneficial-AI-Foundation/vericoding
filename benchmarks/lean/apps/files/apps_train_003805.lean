def get_free_urinals (s : String) : Int := sorry

def hasConsecutiveOnes (chars : List Char) : Bool :=
  match chars with
  | '1' :: '1' :: _ => true
  | _ :: rest => hasConsecutiveOnes rest
  | [] => false

-- <vc-helpers>
-- </vc-helpers>

def containsAdjacentOnes (s : String) : Bool :=
  hasConsecutiveOnes s.data

theorem invalid_adjacent_urinals :
  ∀ s: String, containsAdjacentOnes s → get_free_urinals s = -1 := sorry

theorem result_nonnegative_if_valid :
  ∀ s: String, ¬containsAdjacentOnes s → get_free_urinals s ≥ 0 := sorry

theorem result_bounded_by_half_length :
  ∀ s: String, ¬containsAdjacentOnes s → 
    get_free_urinals s ≤ (s.length + 1) / 2 := sorry

theorem alternating_pattern_valid :
  ∀ gaps: List Nat,
  let s := String.join (List.intersperse "0" (List.replicate gaps.length "1"))
  ¬containsAdjacentOnes s →
  get_free_urinals s ≥ 0 := sorry

/-
info: 1
-/
-- #guard_msgs in
-- #eval get_free_urinals "10001"

/-
info: 3
-/
-- #guard_msgs in
-- #eval get_free_urinals "00000"

/-
info: -1
-/
-- #guard_msgs in
-- #eval get_free_urinals "110"

-- Apps difficulty: introductory
-- Assurance level: guarded