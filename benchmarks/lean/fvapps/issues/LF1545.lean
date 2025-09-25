-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def find_website_groups (urls : List String) : List (List String) := sorry

theorem groups_return_type (urls : List String) : 
  let result := find_website_groups urls
  result.all (fun group => group.all (fun _ => true)) := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem groups_min_size (urls : List String) :
  let result := find_website_groups urls
  result.all (fun group => group.length > 1) := sorry

theorem hostnames_appear_once (urls : List String) :
  let result := find_website_groups urls
  let all_hostnames := result.bind id
  all_hostnames.length = (all_hostnames.eraseDups).length := sorry

theorem empty_paths_normalized (urls : List String) (h : String) :
  let test_urls := urls ++ [s!"http://{h}", s!"http://{h}/"]
  let result := find_website_groups test_urls
  result.all (fun group => 
    if group.contains h then group.count h = 1 
    else true) := sorry

/-
info: 1
-/
-- #guard_msgs in
-- #eval len find_website_groups(test1)

/-
info: {'abacaba.ru', 'abacaba.de'}
-/
-- #guard_msgs in
-- #eval set result1[0]

/-
info: 1
-/
-- #guard_msgs in
-- #eval len find_website_groups(test2)

/-
info: {'cba.com', 'ccc.bbbb'}
-/
-- #guard_msgs in
-- #eval set result2[0]

/-
info: 1
-/
-- #guard_msgs in
-- #eval len find_website_groups(test3)

/-
info: {'abacaba.com', 'abacaba.de'}
-/
-- #guard_msgs in
-- #eval set result3[0]
-- </vc-theorems>