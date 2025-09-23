-- <vc-preamble>
def WordDictionary.addWord (wd : WordDictionary) (word : String) : WordDictionary :=
  sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def WordDictionary.search (wd : WordDictionary) (pattern : String) : Bool :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem exact_match_property (words : List String) (h : ∀ w ∈ words, w.length > 0) :
  let wd := words.foldl (fun acc word => WordDictionary.addWord acc word) default
  ∀ w ∈ words, (WordDictionary.search wd w) = true :=
  sorry

theorem wildcard_search_property 
  (words : List String) 
  (pattern : String)
  (h1 : words.length > 0)
  (h2 : pattern.length > 0)
  (h3 : ∀ w ∈ words, w.length > 0) :
  let wd := words.foldl (fun acc word => WordDictionary.addWord acc word) default
  let matching_words := words.filter (fun w => w.length = pattern.length)
  matching_words.length > 0 →
  (WordDictionary.search wd pattern) = 
    matching_words.any (fun word =>
      let pairs := List.zip (pattern.data) (word.data)
      pairs.all (fun pair => pair.fst = '.' ∨ pair.fst = pair.snd)) :=
  sorry
-- </vc-theorems>