-- <vc-helpers>
-- </vc-helpers>

def word_count (text : String) : Nat := sorry

def OMIT : List String := ["a", "the", "on", "at", "of", "upon", "in", "as"]

theorem word_count_with_valid_words (text : String) (words : List String) 
  (h1 : ∀ w ∈ words, ∀ c ∈ w.data, 'a' ≤ c ∧ c ≤ 'z')
  (h2 : text = String.join (List.intersperse " " words))
  (h3 : words ≠ []) :
  word_count text = (words.filter (fun w => !OMIT.contains w)).length := sorry

theorem omitted_words_count_zero (text : String) (words : List String)
  (h1 : ∀ w ∈ words, OMIT.contains w)  
  (h2 : words ≠ [])
  (h3 : text = String.join (List.intersperse " " words)) :
  word_count text = 0 := sorry

theorem word_count_empty : word_count "" = 0 := sorry

theorem word_count_spaces : word_count "   " = 0 := sorry 

theorem word_count_special_chars : word_count "!@#$%^&*()" = 0 := sorry

/-
info: 2
-/
-- #guard_msgs in
-- #eval word_count "hello there"

/-
info: 4
-/
-- #guard_msgs in
-- #eval word_count "Hello there, little user5453 374 ())$."

/-
info: 112
-/
-- #guard_msgs in
-- #eval word_count "I"d been using my sphere as a stool. I traced counterclockwise circles on it with my fingertips and it shrank until I could palm it. My bolt had shifted while I"d been sitting. I pulled it up and yanked the pleats straight as I careered around tables, chairs, globes, and slow-moving fraas. I passed under a stone arch into the Scriptorium. The place smelled richly of ink. Maybe it was because an ancient fraa and his two fids were copying out books there. But I wondered how long it would take to stop smelling that way if no one ever used it at all; a lot of ink had been spent there, and the wet smell of it must be deep into everything."

-- Apps difficulty: introductory
-- Assurance level: unguarded