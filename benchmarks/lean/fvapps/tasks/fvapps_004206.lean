-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def cookie {α : Type u} (x : α) : String := sorry

theorem cookie_on_string (s : String) :
  cookie s = "Who ate the last cookie? It was Zach!" := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem cookie_on_float (f : Float) :
  cookie f = "Who ate the last cookie? It was Monica!" := sorry

theorem cookie_on_int (i : Int) :
  cookie i = "Who ate the last cookie? It was Monica!" := sorry

theorem cookie_on_other {α : Type} (x : α) 
  (h1 : α ≠ String) (h2 : α ≠ Float) (h3 : α ≠ Int) :
  cookie x = "Who ate the last cookie? It was the dog!" := sorry
-- </vc-theorems>