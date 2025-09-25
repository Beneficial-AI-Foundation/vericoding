-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def smallest_lexicographic_string (n l : Nat) (strings : List String) : String := sorry

def strRepeat (s : String) (n : Nat) : String := 
  match n with
  | 0 => ""
  | n + 1 => s ++ strRepeat s n
-- </vc-definitions>

-- <vc-theorems>
theorem smallest_lexicographic_string_properties 
  {n l : Nat} {strings : List String}
  (hn : 1 ≤ n ∧ n ≤ 5)
  (hl : 1 ≤ l ∧ l ≤ 5)
  (hstrings : strings.length = n)
  (hstringsLen : ∀ s ∈ strings, s.length = l)
  : let result := smallest_lexicographic_string n l strings;
    -- Result contains all input strings
    (∀ s ∈ strings, s ∈ result.splitOn "")
    -- Length is n * l
    ∧ result.length = n * l
    -- Result parts are sorted
    ∧ List.length (result.splitOn "") = n := sorry

theorem empty_and_single_char_strings
  {n l : Nat}
  (hn : 1 ≤ n ∧ n ≤ 5)
  (hl : 1 ≤ l ∧ l ≤ 5)
  : smallest_lexicographic_string n l (List.replicate n (strRepeat "a" l)) = strRepeat "a" (n * l) := sorry

theorem single_string
  {n : Nat}
  (hn : 1 ≤ n ∧ n ≤ 10)
  : smallest_lexicographic_string n 1 (List.replicate n "z") = strRepeat "z" n := sorry
-- </vc-theorems>