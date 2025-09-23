-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def meme_sorting (s : String) : String := sorry

theorem meme_sorting_returns_valid_name (s : String) : 
  meme_sorting s = "Roma" ∨ meme_sorting s = "Maxim" ∨ meme_sorting s = "Danik" ∨ meme_sorting s = "Vlad" := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem bug_pattern_returns_roma {s : String} (h : ∃ i j k : String.Pos, 
  s.get i = 'b' ∧ 
  s.get j = 'u' ∧ 
  s.get k = 'g' ∧
  i < j ∧ j < k) :
  meme_sorting s = "Roma" := sorry

theorem boom_pattern_returns_maxim {s : String} (h : ∃ i j k l : String.Pos,
  s.get i = 'b' ∧
  s.get j = 'o' ∧ 
  s.get k = 'o' ∧
  s.get l = 'm' ∧
  i < j ∧ j < k ∧ k < l) :
  meme_sorting s = "Maxim" := sorry

theorem edits_pattern_returns_danik {s : String} (h : ∃ i j k l m : String.Pos,
  s.get i = 'e' ∧
  s.get j = 'd' ∧
  s.get k = 'i' ∧
  s.get l = 't' ∧
  s.get m = 's' ∧
  i < j ∧ j < k ∧ k < l ∧ l < m) :
  meme_sorting s = "Danik" := sorry

theorem no_pattern_returns_vlad {s : String} 
  (h1 : ¬∃ i j k : String.Pos, s.get i = 'b' ∧ s.get j = 'u' ∧ s.get k = 'g' ∧ i < j ∧ j < k)
  (h2 : ¬∃ i j k l : String.Pos, s.get i = 'b' ∧ s.get j = 'o' ∧ s.get k = 'o' ∧ s.get l = 'm' ∧ i < j ∧ j < k ∧ k < l)
  (h3 : ¬∃ i j k l m : String.Pos, s.get i = 'e' ∧ s.get j = 'd' ∧ s.get k = 'i' ∧ s.get l = 't' ∧ s.get m = 's' ∧ i < j ∧ j < k ∧ k < l ∧ l < m) :
  meme_sorting s = "Vlad" := sorry

theorem case_insensitive (s1 s2 : String) (h : s1.toLower = s2.toLower) :
  meme_sorting s1 = meme_sorting s2 := sorry
-- </vc-theorems>