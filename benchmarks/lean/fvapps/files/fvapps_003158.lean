-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def cypher (s : String) : String := sorry

theorem cypher_length_preserved (s : String) : 
  (cypher s).length = s.length := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem cypher_idempotent (s : String) :
  cypher (cypher s) = cypher s := sorry

theorem cypher_maps_chars_correctly (s : String) :
  cypher s = s.map (fun c => match c with
    | 'I' => '1' | 'R' => '2' | 'E' => '3' | 'A' => '4' 
    | 'S' => '5' | 'G' => '6' | 'T' => '7' | 'B' => '8'
    | 'l' => '1' | 'z' => '2' | 'e' => '3' | 'a' => '4'
    | 's' => '5' | 'b' => '6' | 't' => '7' | 'g' => '9'
    | 'o' => '0' | 'O' => '0'
    | c => c) := sorry

theorem cypher_preserves_unmapped (s : String) (c : Char) :
  c ∉ ['I', 'R', 'E', 'A', 'S', 'G', 'T', 'B', 'l', 'z', 'e', 'a', 's', 'b', 't', 'g', 'o', 'O'] →
  (c ∈ s.data → c ∈ (cypher s).data) := sorry
-- </vc-theorems>