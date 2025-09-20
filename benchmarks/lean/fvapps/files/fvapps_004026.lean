-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (files : List String) : List String := sorry

theorem empty_list_gives_empty_result :
  solve [] = [] := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem single_txt_file_gives_txt_extension :
  solve ["test1.txt"] = [".txt"] := sorry

theorem multiple_files_same_extension :
  solve ["a.txt", "b.txt", "c.mp3"] = [".txt"] := sorry

theorem multiple_files_multiple_extensions :
  solve ["a.txt", "b.txt", "c.mp3", "d.mp3"] = [".mp3", ".txt"] := sorry
-- </vc-theorems>