-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def countCharacters : List String → String → Nat :=
  sorry

def String.count (s : String) (c : Char) : Nat :=
sorry
-- </vc-definitions>

-- <vc-theorems>
def canForm (w : String) (chars : String) : Bool :=
  let check (c : Char) := w.count c ≤ chars.count c
  w.data.all check

theorem count_characters_nonnegative (words : List String) (chars : String) :
  countCharacters words chars ≥ 0 := by
sorry

theorem count_characters_bounded_by_total_length (words : List String) (chars : String) :
  countCharacters words chars ≤ (words.map String.length).foldl (· + ·) 0 := by
sorry

theorem count_characters_empty_chars (words : List String) :
  countCharacters words "" = 0 := by
sorry

theorem count_characters_monotone (words : List String) (chars s : String) :
  countCharacters words (chars ++ s) ≥ countCharacters words chars := by
sorry

theorem count_characters_substring_property (words : List String) (chars : String) :
  countCharacters words chars =
    (List.map String.length
      (List.filter (fun w => canForm w chars) words)).foldl (· + ·) 0 := by
sorry
-- </vc-theorems>