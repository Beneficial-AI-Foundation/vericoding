-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def word_to_bin (s : String) : List String := sorry

theorem word_to_bin_length {s : String} (h : s.length > 0) : 
  (word_to_bin s).length = s.length := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem word_to_bin_binary_format {s : String} (h : s.length > 0) :
  ∀ x ∈ word_to_bin s,
    x.length = 8 ∧ 
    ∀ c ∈ x.data, c = '0' ∨ c = '1' := sorry

theorem word_to_bin_roundtrip {s : String} (h : s.length > 0) :
  let binList := word_to_bin s
  let decoded := binList.map (fun x => String.toNat! x)
  String.mk (decoded.map Char.ofNat) = s := sorry
-- </vc-theorems>