-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def spoonerize (s : String) : String := sorry

theorem spoonerize_preserves_string_type {s : String} :
  s.contains ' ' ∧ (s.split (· == ' ')).length = 2 →
  spoonerize s ≠ "" := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem spoonerize_single_space {s : String} :
  s.contains ' ' ∧ (s.split (· == ' ')).length = 2 →
  ((spoonerize s).data.filter (· == ' ')).length = 1 := sorry

theorem spoonerize_preserves_length {s : String} :
  s.contains ' ' ∧ (s.split (· == ' ')).length = 2 →
  (spoonerize s).length = s.length := sorry

theorem spoonerize_preserves_chars {s : String} :
  s.contains ' ' ∧ (s.split (· == ' ')).length = 2 →
  ∀ c, (s.data.filter (· == c)).length = ((spoonerize s).data.filter (· == c)).length := sorry

theorem spoonerize_swaps_first_letters {s : String} (w1 w2 : String)
  (h : s = w1 ++ String.mk [' '] ++ w2) (hw : w1 ≠ "" ∧ w2 ≠ "") :
  let r := spoonerize s
  let r1 := (r.split (· == ' ')).get! 0
  let r2 := (r.split (· == ' ')).get! 1
  r1.get! 0 = w2.get! 0 ∧ r2.get! 0 = w1.get! 0 := sorry

theorem spoonerize_preserves_rest {s : String} (w1 w2 : String)
  (h : s = w1 ++ String.mk [' '] ++ w2) (hw : w1 ≠ "" ∧ w2 ≠ "") :
  let r := spoonerize s
  let r1 := (r.split (· == ' ')).get! 0
  let r2 := (r.split (· == ' ')).get! 1
  List.drop 1 r1.data = List.drop 1 w1.data ∧ 
  List.drop 1 r2.data = List.drop 1 w2.data := sorry

theorem spoonerize_invalid_empty (s : String) :
  s = "" → spoonerize s = "" := sorry

theorem spoonerize_invalid_one_word (s : String) :
  (¬s.contains ' ') → spoonerize s = "" := sorry

theorem spoonerize_invalid_too_many (s : String) :
  (s.split (· == ' ')).length > 2 → spoonerize s = "" := sorry
-- </vc-theorems>