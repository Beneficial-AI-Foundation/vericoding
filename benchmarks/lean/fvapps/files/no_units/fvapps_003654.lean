-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def unique_date (a b c : Int) : String := sorry

def is_valid_date (y m d : Int) : Bool := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem unique_date_output_format (a b c : Int) 
  (h1 : 0 ≤ a ∧ a ≤ 99)
  (h2 : 0 ≤ b ∧ b ≤ 99) 
  (h3 : 0 ≤ c ∧ c ≤ 99) :
  let result := unique_date a b c
  (result = "ambiguous" ∨ result = "invalid") ∨
  (result.length = 8 ∧ 
   result.get ⟨2⟩ = '/' ∧
   result.get ⟨5⟩ = '/' ∧
   let split := result.splitOn "/"
   let y := String.toInt! split[0]!
   let m := String.toInt! split[1]!
   let d := String.toInt! split[2]!
   is_valid_date y m d) := sorry

theorem unique_date_guaranteed_valid 
  (month day year : Int)
  (h1 : 1 ≤ month ∧ month ≤ 12)
  (h2 : 1 ≤ day ∧ day ≤ 28)
  (h3 : 0 ≤ year ∧ year ≤ 99) :
  let result := unique_date month day year
  result = "ambiguous" ∨
  String.toInt! (result.splitOn "/")[0]! = year := sorry

theorem unique_date_all_invalid
  (a b c : Int)
  (h1 : 32 ≤ a ∧ a ≤ 99)
  (h2 : 32 ≤ b ∧ b ≤ 99)
  (h3 : 32 ≤ c ∧ c ≤ 99) :
  unique_date a b c = "invalid" := sorry
-- </vc-theorems>