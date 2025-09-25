-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def get_key_length (text : String) (max_length : Int) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem single_char_key_min_one {text : String} (h : text.length ≥ 1) :
  get_key_length (text ++ text ++ text) 5 ≥ 1 :=
sorry

theorem repeating_pattern_bounds {text : String} {n max_len : Nat} 
  (h1 : text.length ≥ 2) (h2 : n ≥ 1) (h3 : n ≤ 20)
  (h4 : max_len = text.length + 5) :
  let result := get_key_length (String.join (List.replicate n text)) max_len
  1 ≤ result ∧ result ≤ text.length :=
sorry 

theorem periodic_sequence {n : Nat} (h : n ≥ 1) (h2 : n ≤ 100) :
  let text := String.join (List.replicate n "AB")
  let result := get_key_length text n
  result = 1 ∨ result = 2 :=
sorry

theorem key_length_bounds {text : String} {key_length : Nat}
  (h1 : text.length ≥ 1) (h2 : key_length ≥ 1) (h3 : key_length ≤ 10) :
  let result := get_key_length text key_length
  1 ≤ result ∧ result ≤ min key_length text.length :=
sorry
-- </vc-theorems>