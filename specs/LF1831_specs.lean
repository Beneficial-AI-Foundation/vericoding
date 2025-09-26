-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def WordFilter.new (words : List String) : WordFilter := sorry

def mkString : List Char → String := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem wordfilter_result_bounds (words : List String) (wf : WordFilter)
    (h : words ≠ []) (p s : String) :
  wf.f p s ≤ words.length := sorry

theorem wordfilter_match_criteria (words : List String) (wf : WordFilter)
    (h : words ≠ []) (p s : String)
    (startsWith endsWith : String → String → Bool)
    (h3 : wf.f p s < words.length) :
  let matching_word := words.get! (wf.f p s)
  startsWith matching_word p ∧ endsWith matching_word s := sorry

theorem wordfilter_last_match (words : List String) (wf : WordFilter)
    (h : words ≠ []) (p s : String)
    (startsWith endsWith : String → String → Bool)
    (h3 : wf.f p s < words.length) :
  ∀ i, wf.f p s < i → i < words.length →
  ¬(startsWith (words.get! i) p ∧ endsWith (words.get! i) s) := sorry

theorem wordfilter_empty_strings (words : List String) (wf : WordFilter)
    (h : words ≠ []) :
  wf.f "" "" = words.length - 1 := sorry

theorem wordfilter_impossible_match (words : List String) (wf : WordFilter)
    (h : words ≠ []) (maxLen : Nat) (len : String → Nat)
    (h2 : maxLen = words.foldl (fun m w => max m (len w)) 0) :
  wf.f (mkString (List.replicate (maxLen + 1) 'a')) "" = words.length := sorry
-- </vc-theorems>