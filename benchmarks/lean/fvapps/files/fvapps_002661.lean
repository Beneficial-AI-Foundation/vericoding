-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def String.hasSubstring (s1 s2 : String) : Bool :=
  sorry

def areYouPlayingBanjo (name : String) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem banjo_output_format (name : String) (h : name.length > 0) :
  let result := areYouPlayingBanjo name
  result.startsWith name ∧
  result.endsWith "banjo" ∧
  (result.hasSubstring " plays banjo" ∨ result.hasSubstring " does not play banjo") :=
sorry

theorem starts_with_r_plays_banjo (name : String) (h1 : name.length > 0)
    (h2 : name.front = 'r' ∨ name.front = 'R') :
  (areYouPlayingBanjo name).hasSubstring " plays banjo" = true :=
sorry

theorem not_r_does_not_play_banjo (name : String) (h1 : name.length > 0)
    (h2 : name.front ≠ 'r' ∧ name.front ≠ 'R') :
  (areYouPlayingBanjo name).hasSubstring " does not play banjo" = true :=
sorry
-- </vc-theorems>