-- <vc-preamble>
def countChar (s: String) (c: Char) : Nat :=
  s.foldl (fun acc x => if x = c then acc + 1 else acc) 0

def makeZeroLine (width: Nat) : String :=
  String.mk (List.replicate width '0')

def makeZeroGrid (width height: Nat) : String :=
  String.intercalate "\r\n" (List.replicate height (makeZeroLine width))
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def interpreter (code: String) (iterations width height: Nat) : String := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem valid_dimensions (code: String) (iterations width height: Nat) :
  let result := interpreter code iterations width height
  let lines := result.splitOn "\r\n"
  lines.length = height ∧
  lines.all (fun line => line.length = width)
  :=
sorry

theorem valid_output_chars (code: String) (iterations width height: Nat) :
  let result := interpreter code iterations width height
  let lines := result.splitOn "\r\n"
  lines.all (fun line => line.all (fun c => c = '0' ∨ c = '1'))
  :=
sorry

theorem empty_code (width height: Nat) :
  let result := interpreter "" 0 width height
  result = makeZeroGrid width height
  :=
sorry

theorem zero_iterations (code: String) (width height: Nat) :
  let result := interpreter code 0 width height
  result = makeZeroGrid width height
  :=
sorry

theorem valid_brackets (code: String) (iterations width height: Nat) :
  (countChar code '[' = countChar code ']') →
  ∃ x, x = interpreter code iterations width height
  :=
sorry
-- </vc-theorems>