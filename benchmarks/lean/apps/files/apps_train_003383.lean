/-
You have to write a function that describe Leo:
```python
def leo(oscar):
  pass
```

if oscar was (integer) 88, you have to return "Leo finally won the oscar! Leo is happy".
if oscar was 86, you have to return "Not even for Wolf of wallstreet?!"
if it was not 88 or 86 (and below 88) you should return "When will you give Leo an Oscar?"
if it was over 88 you should return "Leo got one already!"
-/

-- <vc-helpers>
-- </vc-helpers>

def leo (oscar : Int) : String := sorry

theorem leo_is_string (oscar : Int) :
  ∃ s : String, leo oscar = s := sorry

theorem leo_before_wolf (oscar : Int) (h: oscar ≤ 85) :
  leo oscar = "When will you give Leo an Oscar?" := sorry

theorem leo_after_win (oscar : Int) (h: oscar ≥ 89) :
  leo oscar = "Leo got one already!" := sorry

theorem leo_edge_cases :
  leo 86 = "Not even for Wolf of wallstreet?!" ∧
  leo 88 = "Leo finally won the oscar! Leo is happy" := sorry

/-
info: 'Leo finally won the oscar! Leo is happy'
-/
-- #guard_msgs in
-- #eval leo 88

/-
info: 'When will you give Leo an Oscar?'
-/
-- #guard_msgs in
-- #eval leo 87

/-
info: 'Not even for Wolf of wallstreet?!'
-/
-- #guard_msgs in
-- #eval leo 86

-- Apps difficulty: introductory
-- Assurance level: unguarded