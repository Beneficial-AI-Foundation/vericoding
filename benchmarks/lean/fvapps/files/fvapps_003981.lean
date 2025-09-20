-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def vowel_shift (s : Option String) (n : Int) : Option String := sorry

theorem empty_cases (n : Int) : 
  vowel_shift none n = none ∧ 
  vowel_shift (some "") n = some "" := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem zero_shift (s : String) :
  vowel_shift (some s) 0 = some s := sorry

theorem full_rotation {s : String} (h : s ≠ "") :
  let vowel_count := (s.data.filter (fun c => ['a', 'e', 'i', 'o', 'u'].contains c.toLower)).length
  vowel_count > 0 → 
  vowel_shift (some s) vowel_count = some s := sorry

theorem shift_composition {s : String} (h : s ≠ "") (n1 n2 : Int) 
  (h1 : n1 ≥ -100) (h2 : n1 ≤ 100) (h3 : n2 ≥ -100) (h4 : n2 ≤ 100) :
  match vowel_shift (some s) n1 with
  | none => True
  | some s1 => 
    match vowel_shift (some s1) n2 with
    | none => True
    | some s2 => s2 = (vowel_shift (some s) (n1 + n2)).get!
  := sorry
-- </vc-theorems>