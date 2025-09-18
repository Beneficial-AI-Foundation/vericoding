-- <vc-preamble>
def ValidWords := ["nil", "one", "two", "three", "four", "five", "six", "seven", "eight", "nine"]

def WordToNum : String → Nat
  | "nil" => 0
  | "one" => 1 
  | "two" => 2
  | "three" => 3
  | "four" => 4
  | "five" => 5
  | "six" => 6
  | "seven" => 7
  | "eight" => 8
  | "nine" => 9
  | _ => 0
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def scoreboard (s : String) : List Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem scoreboard_output_valid (s : String) :
  let result := scoreboard s
  ∀ x ∈ result, 0 ≤ x ∧ x ≤ 9 :=
  sorry
-- </vc-theorems>