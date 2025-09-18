-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def multiple_split (s : String) (delims : List String) : List String :=
  sorry

def containsString (s : String) (sub : String) : Bool :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem multiple_split_nonempty_parts
  (s : String) (delims : List String)
  : ∀ (x : String), x ∈ multiple_split s delims → x.length > 0
  := by
sorry

theorem multiple_split_no_delims_in_result
  (s : String) (delims : List String)
  : ∀ (x : String) (d : String),
    x ∈ multiple_split s delims →
    d ∈ delims →
    ¬ containsString x d
  := by
sorry

theorem multiple_split_empty_string
  (delims : List String)
  : multiple_split "" delims = []
  := by
sorry

theorem multiple_split_empty_delims
  (s : String)
  : multiple_split s [] = if s = "" then [] else [s]
  := by
sorry

theorem multiple_split_single_delim
  (s : String) (delim : String)
  (h : delim.length > 0)
  : multiple_split s [delim] = (s.split (· == '.')).filter (fun x => x ≠ "")
  := by
sorry
-- </vc-theorems>