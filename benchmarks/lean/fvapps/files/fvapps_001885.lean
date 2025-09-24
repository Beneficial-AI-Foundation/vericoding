-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def remove_subfolders (folders: List String) : List String :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem empty_folder_list : remove_subfolders [] = [] :=
sorry

theorem single_folder_unchanged (a : String) : 
  remove_subfolders [a] = [a] :=
sorry

theorem folder_with_subfolder : 
  remove_subfolders ["/a", "/a/b"] = ["/a"] :=
sorry

theorem separate_folders : 
  remove_subfolders ["/a", "/b"] = ["/a", "/b"] :=
sorry

theorem result_subset (folders : List String) :
  ∀ x, x ∈ remove_subfolders folders → x ∈ folders :=
sorry

theorem result_ascending (folders : List String) :
  ∀ i j, i < j → 
  List.get! (remove_subfolders folders) i ≤ List.get! (remove_subfolders folders) j :=
sorry

theorem no_subfolders_in_result (folders : List String) :
  ∀ p1 p2, p1 ∈ remove_subfolders folders → 
  p2 ∈ remove_subfolders folders →
  p1 ≠ p2 → ¬(p2.startsWith (p1 ++ "/")) :=
sorry
-- </vc-theorems>