-- <vc-helpers>
-- </vc-helpers>

def count_decodings (s : String) : String := sorry

theorem single_valid_mapping_returns_yes_or_no (n : Nat) 
  (h : 1 ≤ n ∧ n ≤ 26) :
  let s := toString n
  count_decodings s = "YES" ∨ count_decodings s = "NO" := sorry

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible