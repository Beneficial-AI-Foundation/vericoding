-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def String.words (s : String) : List String := sorry
def encode (s : String) : String := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem encode_preserves_spaces {s : String} : 
  (s.words).length = (encode s).words.length := sorry

theorem encode_single_char_unchanged {s : String} :
  s.length = 1 → encode s = s := sorry

theorem encode_preserves_last_chars {s : String} {w : String} :
  w ∈ s.words → w.length > 0 →
  (((encode s).words).find? (· = w)).map String.back = some w.back := sorry 

theorem encode_idempotent {s : String} :
  encode (encode s) = encode s ↔ 
  ∀ w ∈ s.words, w.length ≤ 2 := sorry
-- </vc-theorems>