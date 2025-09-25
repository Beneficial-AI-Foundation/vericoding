-- <vc-preamble>
def isVowel (c : Char) : Bool :=
  c == 'a' || c == 'e' || c == 'i' || c == 'o' || c == 'u'
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (s : String) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem output_format {s : String} (h : s.length > 0) :
  let result := solve s
  (result = "failed") ∨ 
  (∀ c, c ∈ result.data → c ∈ s.data) := 
  sorry

theorem alternating_pattern {s : String} (h : s.length > 0) :
  let result := solve s
  result ≠ "failed" → result.length > 1 →
  ∀ i : Fin result.length, i.val + 1 < result.length →
    ∀ pos pos' : String.Pos, 
      pos.byteIdx = i.val → pos'.byteIdx = i.val + 1 →
      isVowel (result.get pos) ≠ isVowel (result.get pos') :=
  sorry
-- </vc-theorems>