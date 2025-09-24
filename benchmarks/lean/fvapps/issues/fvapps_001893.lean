-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def defaultMagicDictionary : MagicDictionary := {
  l := []
  buildDict := fun words => words
  search := fun _ => false
}
-- </vc-definitions>

-- <vc-theorems>
theorem buildDict_preserves_words (md : MagicDictionary) (words : List String) : 
  md.buildDict words = words := sorry

theorem length_mismatch_returns_false (md : MagicDictionary) (word : String) (delta : Nat) :
  delta ≥ 1 →
  ¬(md.search (word ++ String.mk (List.replicate delta 'a'))) := sorry

theorem single_char_diff_returns_true (md : MagicDictionary) (word : String) (pos : Nat) :
  pos < word.length →
  let newChar := if word.get ⟨pos⟩ = 'x' then 'y' else 'x'
  let modified := word.set ⟨pos⟩ newChar
  md.search modified := sorry
-- </vc-theorems>