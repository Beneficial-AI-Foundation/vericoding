-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def warn_the_sheep (queue : List String) : String := sorry

theorem wolf_at_end_gives_warning_message {queue : List String} 
  (h : queue = queue.dropLast ++ [("wolf" : String)]) :
  warn_the_sheep queue = "Pls go away and stop eating my sheep" := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem wolf_with_sheep_after_gives_warning {queue : List String}
  (h1 : ∃ i, queue.get? i = some "wolf")
  (h2 : ∃ n, n > 0 ∧ queue.length = (queue.indexOf "wolf" + 1 + n)) :
  let sheep_after := queue.length - queue.indexOf "wolf" - 1
  warn_the_sheep queue = s!"Oi! Sheep number {sheep_after}! You are about to be eaten by a wolf!" := sorry
-- </vc-theorems>