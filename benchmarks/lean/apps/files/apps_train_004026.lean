-- <vc-helpers>
-- </vc-helpers>

def solve (files : List String) : List String := sorry

theorem empty_list_gives_empty_result :
  solve [] = [] := sorry

theorem single_txt_file_gives_txt_extension :
  solve ["test1.txt"] = [".txt"] := sorry

theorem multiple_files_same_extension :
  solve ["a.txt", "b.txt", "c.mp3"] = [".txt"] := sorry

theorem multiple_files_multiple_extensions :
  solve ["a.txt", "b.txt", "c.mp3", "d.mp3"] = [".mp3", ".txt"] := sorry

/-
info: ['.als', '.mp3']
-/
-- #guard_msgs in
-- #eval solve ["Lakey - Better days.mp3", "Wheathan - Superlove.wav", "groovy jam.als", "#4 final mixdown.als", "album cover.ps", "good nights.mp3"]

/-
info: ['.mp3']
-/
-- #guard_msgs in
-- #eval solve ["Lakey - Better days.mp3", "Fisher - Stop it.mp3", "Fisher - Losing it.mp3", "#4 final mixdown.als", "album cover.ps", "good nights.mp3"]

/-
info: []
-/
-- #guard_msgs in
-- #eval solve []

-- Apps difficulty: introductory
-- Assurance level: unguarded