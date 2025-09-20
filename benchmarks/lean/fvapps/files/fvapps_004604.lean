-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def isAlpha (c : Char) : Bool := sorry

def letterFrequency (s : String) : List (Char × Nat) := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem letterFrequency_output_structure 
  (s : String) :
  let result := letterFrequency s
  ∀ pair, pair ∈ result → 
    isAlpha pair.fst ∧ 
    pair.snd > 0 := sorry

theorem letterFrequency_ordering 
  (s : String) :
  let result := letterFrequency s  
  result ≠ [] →
  ∀ (i : Fin result.length) (j : Fin result.length),
    i.val < j.val →
    ((result.get i).snd > (result.get j).snd ∨ 
    ((result.get i).snd = (result.get j).snd ∧ 
     (result.get i).fst < (result.get j).fst)) := sorry

theorem letterFrequency_total_count
  (s : String) :
  let result := letterFrequency s
  List.foldl (λ acc pair => acc + pair.snd) 0 result = 
  List.length (s.data.filter isAlpha) := sorry
-- </vc-theorems>