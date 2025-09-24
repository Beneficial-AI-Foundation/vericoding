-- <vc-preamble>
def valid_letters := ['w', 'p', 'b', 's', 'm', 'q', 'd', 'z']

def score_map (c : Char) : Int :=
  match c with
  | 'w' => 4
  | 'p' => 3
  | 'b' => 2
  | 's' => 1
  | 'm' => -4
  | 'q' => -3
  | 'd' => -2
  | 'z' => -1
  | _ => 0
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def alphabet_war (s : String) : String :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem alphabet_war_valid_output (s : String) :
  alphabet_war s = "Left side wins!" ∨
  alphabet_war s = "Right side wins!" ∨
  alphabet_war s = "Let's fight again!" :=
sorry

theorem alphabet_war_invalid_chars (s : String) :
  alphabet_war s = "Left side wins!" ∨
  alphabet_war s = "Right side wins!" ∨
  alphabet_war s = "Let's fight again!" :=
sorry

theorem alphabet_war_scoring (s : String) (h : s.all (λ c => c ∈ valid_letters)) :
  let score := s.foldr (λ c acc => acc + score_map c) 0
  if score > 0 then
    alphabet_war s = "Left side wins!"
  else if score < 0 then
    alphabet_war s = "Right side wins!"
  else
    alphabet_war s = "Let's fight again!" :=
sorry

theorem alphabet_war_opposing_sides (left right : String)
  (h1 : left.all (λ c => c ∈ ['w', 'p', 'b', 's']))
  (h2 : right.all (λ c => c ∈ ['m', 'q', 'd', 'z'])) :
  alphabet_war (left ++ right) = "Left side wins!" ∨
  alphabet_war (left ++ right) = "Right side wins!" ∨
  alphabet_war (left ++ right) = "Let's fight again!" :=
sorry
-- </vc-theorems>