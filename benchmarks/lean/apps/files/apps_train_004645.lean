-- <vc-preamble>
def isAlpha (s : String) : Bool := 
  sorry
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def nato (s : String) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem nato_output_format {s : String} 
  (h : s.all (fun c => c.isAlpha)) :
  let result := nato s
  let words := result.split (· = ' ')
  (∀ w ∈ words, isAlpha w ∨ w.contains '-') ∧ 
  words.length = s.length :=
sorry

theorem nato_case_insensitive {s : String}
  (h : s.all (fun c => 'A' ≤ c ∧ c ≤ 'Z')) :
  nato s = nato s.toUpper :=
sorry

theorem nato_valid_codes {s : String}
  (h : s.all (fun c => 'A' ≤ c ∧ c ≤ 'Z')) :
  let natoWords := ["Alpha", "Bravo", "Charlie", "Delta", "Echo", 
                   "Foxtrot", "Golf", "Hotel", "India", "Juliett",
                   "Kilo", "Lima", "Mike", "November", "Oscar", 
                   "Papa", "Quebec", "Romeo", "Sierra", "Tango",
                   "Uniform", "Victor", "Whiskey", "X-ray", 
                   "Yankee", "Zulu"]
  let result := nato s
  ∀ w ∈ result.split (· = ' '), w ∈ natoWords :=
sorry

/-
info: 'Bravo Alpha November Alpha November Alpha'
-/
-- #guard_msgs in
-- #eval nato "Banana"

/-
info: 'Hotel India'
-/
-- #guard_msgs in
-- #eval nato "Hi"

/-
info: 'Alpha Bravo Charlie'
-/
-- #guard_msgs in
-- #eval nato "ABC"
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: unguarded