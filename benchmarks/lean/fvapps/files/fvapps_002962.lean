-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def cal_n_bug (heads : Int) (legs : Int) (wings : Int) : List Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem valid_output_structure_heads_spiders
  (n : Int) :
  let result := cal_n_bug n (n*6) n
  result.length = 3 ∧ 
  (∀ x ∈ result, x ≥ 0 ∨ result = [-1, -1, -1]) :=
sorry

theorem total_creatures_match_heads
  (heads legs wings : Int) :
  let result := cal_n_bug heads legs wings
  result ≠ [-1, -1, -1] →
  result.foldl (init := 0) (·+·) = heads :=
sorry

theorem legs_and_wings_match
  (spider butterfly dragonfly : Int) :
  let total := spider + butterfly + dragonfly
  let legs := spider*8 + butterfly*6 + dragonfly*6 
  let wings := butterfly + dragonfly*2
  cal_n_bug total legs wings = [spider, butterfly, dragonfly] := 
sorry

theorem negative_heads_invalid
  (n : Int) :
  n < 0 →
  cal_n_bug n 0 0 = [-1, -1, -1] :=
sorry

theorem impossible_combinations
  (n : Int) :
  n > 0 →
  cal_n_bug n 3 n = [-1, -1, -1] ∧
  cal_n_bug n (n*8) n = [-1, -1, -1] :=
sorry
-- </vc-theorems>