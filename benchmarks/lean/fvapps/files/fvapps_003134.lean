-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def what_century (year : String) : String := sorry

theorem what_century_valid_suffix {year : String} 
  (h : year.length = 4 ∧ (∀ c ∈ year.data, '0' ≤ c ∧ c ≤ '9')) : 
  let result := what_century year
  (result.endsWith "st" ∨ result.endsWith "nd" ∨ result.endsWith "rd" ∨ result.endsWith "th") := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem what_century_positive {year : String}
  (h : year.length = 4 ∧ (∀ c ∈ year.data, '0' ≤ c ∧ c ≤ '9')) :
  let result := what_century year
  let century_num := (result.dropRight 2).toNat!
  century_num > 0 := sorry

theorem what_century_calculation {year : String}
  (h : year.length = 4 ∧ (∀ c ∈ year.data, '0' ≤ c ∧ c ≤ '9')) :
  let year_num := year.toNat!
  let expected_century := (year_num - 1) / 100 + 1
  let result := what_century year
  let century_num := (result.dropRight 2).toNat!
  century_num = expected_century := sorry

theorem what_century_suffix_rules {year : String}
  (h : year.length = 4 ∧ (∀ c ∈ year.data, '0' ≤ c ∧ c ≤ '9')) :
  let result := what_century year
  let century_num := (result.dropRight 2).toNat!
  (century_num < 20 → result.endsWith "th") ∧
  (century_num ≥ 20 → 
    match century_num % 10 with
    | 1 => result.endsWith "st"
    | 2 => result.endsWith "nd"
    | 3 => result.endsWith "rd"
    | _ => result.endsWith "th"
  ) := sorry
-- </vc-theorems>