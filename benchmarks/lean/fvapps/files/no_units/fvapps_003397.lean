-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def String.count (needle haystack : String) : Nat := sorry

def sea_sick (s : String) : String := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem sea_sick_output_valid (s : String)
    (h : ∀ c : Char, c ∈ s.data → (c = '~' ∨ c = '_'))
    (h_size : s.length > 0) :
  sea_sick s = "Throw Up" ∨ sea_sick s = "No Problem" := sorry

theorem sea_sick_uniform_string (s : String)
    (h : ∀ c : Char, c ∈ s.data → (c = '~' ∨ c = '_'))
    (h_size : s.length > 0)
    (h_uniform : ∀ (i j : Fin s.length), s.data[i.val]'i.isLt = s.data[j.val]'j.isLt) :
  sea_sick s = "No Problem" := sorry

theorem sea_sick_transition_ratio (s : String)
    (h : ∀ c : Char, c ∈ s.data → (c = '~' ∨ c = '_'))
    (h_size : s.length > 0) :
  let transitions := (String.count "~_" s) + (String.count "_~" s)
  let ratio : Float := Float.ofNat transitions / Float.ofNat s.length
  sea_sick s = "Throw Up" ↔ ratio > 0.2 := sorry

theorem sea_sick_all_waves (s : String)
    (h : ∀ c : Char, c ∈ s.data → c = '~')
    (h_size : s.length > 0) :
  sea_sick s = "No Problem" := sorry

theorem sea_sick_all_flat (s : String)
    (h : ∀ c : Char, c ∈ s.data → c = '_')
    (h_size : s.length > 0) :
  sea_sick s = "No Problem" := sorry
-- </vc-theorems>