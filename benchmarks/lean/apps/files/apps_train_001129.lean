-- <vc-helpers>
-- </vc-helpers>

def convert_string (s : String) : String := sorry

theorem result_structure 
    (s : String) :
    let result := convert_string s
    result = "" ∨ 
    (result.data.head? = some '.' ∧
     ∀ part ∈ result.split (· = '.'), part.length ≤ 1) := sorry

theorem vowels_removed
    (s : String) :
    let result := convert_string s
    let vowels := "aeiou".data
    ∀ c ∈ result.data, c ∉ vowels := sorry

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible