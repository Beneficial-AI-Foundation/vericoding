-- <vc-preamble>
def countChar (s : String) (c : Char) : Nat :=
  s.data.filter (· = c) |>.length

def splitLines (s : String) : List String :=
  s.splitOn "\n"

def makeHString (n : Nat) : String :=
  String.mk (List.replicate n 'H')
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def generateLogo (thickness : Nat) : String := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem logo_lines_count (thickness : Nat) (h : thickness > 0) :
  let result := generateLogo thickness
  let lines := splitLines result
  lines.length = thickness + (thickness + 1) + ((thickness + 1)/2) + (thickness + 1) + thickness :=
sorry

theorem logo_valid_chars (thickness : Nat) (h : thickness > 0) :
  let result := generateLogo thickness
  let lines := splitLines result
  ∀ line ∈ lines, ∀ c ∈ line.data, c = 'H' ∨ c = ' ' :=
sorry

theorem logo_first_last_line_H_count (thickness : Nat) (h : thickness > 0) :
  let result := generateLogo thickness
  let lines := splitLines result
  (countChar lines[0]! 'H' = 1) ∧
  (countChar lines[lines.length - 1]! 'H' = 1) :=
sorry

theorem logo_middle_section_solid (thickness : Nat) (h : thickness > 0) :
  let result := generateLogo thickness
  let lines := splitLines result
  let middleStart := thickness + (thickness + 1)
  let middleSection := lines.drop middleStart |>.take ((thickness + 1)/2)
  ∀ line ∈ middleSection, ∀ i ∈ line.data.take (5 * thickness), i = 'H' :=
sorry
-- </vc-theorems>