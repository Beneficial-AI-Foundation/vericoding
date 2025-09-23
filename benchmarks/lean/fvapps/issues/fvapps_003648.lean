-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def word_wrap (text : String) (limit : Nat) : String := sorry

theorem word_wrap_line_length {text : String} {limit : Nat}
  (h_text : ∀ c ∈ text.data, c.isAlpha ∨ c = ' ')
  (h_limit : limit > 0) :
  let result := word_wrap text limit
  ∀ line ∈ result.splitOn "\n", line.length ≤ limit := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem word_wrap_preserves_content {text : String} {limit : Nat}
  (h_text : ∀ c ∈ text.data, c.isAlpha ∨ c = ' ')
  (h_limit : limit > 0) :
  let result := word_wrap text limit
  (String.join (text.splitOn " ")).data = (String.join (result.replace "\n" "" |>.splitOn " ")).data := sorry

theorem single_word_wrap_properties {text : String} {limit : Nat}
  (h_text : ∀ c ∈ text.data, c.isAlpha)
  (h_text_nonempty : text.length > 0)
  (h_limit : limit > 0)
  (h_limit_bound : limit ≤ text.length) :
  let result := word_wrap text limit
  let lines := result.splitOn "\n"
  (∀ i : Fin lines.length, i.val < lines.length - 1 → (lines[i]).length = limit) ∧
  (match lines.get? (lines.length - 1) with
   | none => 0
   | some lastLine => lastLine.length) ≤ limit ∧
  String.join lines = text := sorry

theorem multiple_words_no_splitting {words : List String} {limit : Nat}
  (h_words_nonempty : words ≠ [])
  (h_words_alpha : ∀ w ∈ words, ∀ c ∈ w.data, c.isAlpha)
  (h_max_word := words.map String.length |>.maximum?)
  (h_limit : ∀ w ∈ words, w.length < limit) :
  let text := String.join (List.intersperse " " words)
  let result := word_wrap text limit
  (result.replace "\n" " ").splitOn " " = words := sorry

/-
info: 'test'
-/
-- #guard_msgs in
-- #eval word_wrap "test" 7

/-
info: 'hello\nworld'
-/
-- #guard_msgs in
-- #eval word_wrap "hello world" 7

/-
info: 'areall\nylongw\nord'
-/
-- #guard_msgs in
-- #eval word_wrap "areallylongword" 6
-- </vc-theorems>