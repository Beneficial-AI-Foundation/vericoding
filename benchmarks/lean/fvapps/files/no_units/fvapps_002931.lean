-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def combine : List (String × Int) → List (String × Int) → List (String × Int) := sorry

def combineMulti : List (List (String × Int)) → List (String × Int) := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem combine_key_preservation {d1 d2 : List (String × Int)} :
  ∀ k, (combine d1 d2).any (λ p => p.1 = k) ↔ 
       d1.any (λ p => p.1 = k) ∨ d2.any (λ p => p.1 = k) := sorry

theorem combine_value_sum {d1 d2 : List (String × Int)} (k : String) :
  let v1 := (d1.find? (λ p => p.1 = k)).map Prod.snd |>.getD 0
  let v2 := (d2.find? (λ p => p.1 = k)).map Prod.snd |>.getD 0
  let vr := ((combine d1 d2).find? (λ p => p.1 = k)).map Prod.snd |>.getD 0
  vr = v1 + v2 := sorry

theorem combine_single_dict {d : List (String × Int)} :
  combine d [] = d := sorry 

theorem combine_with_empty {d : List (String × Int)} :
  combine d [] = d ∧ combine [] d = d := sorry

theorem combine_associative {d1 d2 d3 : List (String × Int)} :
  combine (combine d1 d2) d3 = combine d1 (combine d2 d3) := sorry
-- </vc-theorems>