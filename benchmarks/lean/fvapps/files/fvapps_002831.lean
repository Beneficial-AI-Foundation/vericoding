-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def songDecoder (s : String) : String :=
sorry

def isSubstring (sub str : String) : Bool :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem no_wub_in_output (s : String) :
  ¬isSubstring "WUB" (songDecoder s) :=
sorry

theorem no_leading_trailing_spaces (s : String) :
  ¬(songDecoder s).startsWith " " ∧ ¬(songDecoder s).endsWith " " :=
sorry

theorem no_multiple_spaces (s : String) :
  ¬isSubstring "  " (songDecoder s) :=
sorry

theorem idempotent (s : String) :
  songDecoder (songDecoder s) = songDecoder s :=
sorry

theorem output_properties (s : String) :
  let result := songDecoder s
  String.length result ≥ 0 ∧
  ¬isSubstring "  " result ∧
  ¬result.startsWith " " ∧
  ¬result.endsWith " " :=
sorry
-- </vc-theorems>