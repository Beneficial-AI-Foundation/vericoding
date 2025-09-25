-- <vc-preamble>
def makeBalloonsString (n : Nat) : String :=
  String.join (List.replicate n "balloon")
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def max_balloons (s : String) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem max_balloons_nonnegative (text : String) :
  max_balloons text ≥ 0 :=
sorry

theorem max_balloons_upper_bound (text : String) :
  max_balloons text ≤ text.length / 7 :=
sorry

theorem max_balloons_has_needed_chars (text : String) (c : Char) :
  let result := max_balloons text
  let needed := match c with
    | 'b' => result
    | 'a' => result
    | 'l' => 2 * result
    | 'o' => 2 * result
    | 'n' => result
    | _ => 0
  (text.toList.filter (· = c)).length ≥ needed :=
sorry

theorem max_balloons_exact (n : Nat) :
  max_balloons (makeBalloonsString n) = n :=
sorry

theorem max_balloons_no_relevant_chars (text : String)
  (h : ∀ c ∈ text.toList, c ∉ ['b', 'a', 'l', 'o', 'n']) :
  max_balloons text = 0 :=
sorry
-- </vc-theorems>