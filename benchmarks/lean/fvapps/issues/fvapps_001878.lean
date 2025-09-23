-- <vc-preamble>
def BrowserHistory.new (homepage : String) : BrowserHistory := sorry
def BrowserHistory.visit (self : BrowserHistory) (url : String) : BrowserHistory := sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def BrowserHistory.back (self : BrowserHistory) (steps : Nat) : (BrowserHistory × String) := sorry
def BrowserHistory.forward (self : BrowserHistory) (steps : Nat) : (BrowserHistory × String) := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem browser_history_init (homepage : String) :
  let browser := BrowserHistory.new homepage
  browser.hashM[0]! = homepage ∧ 
  browser.currIndex = 0 ∧
  browser.maxIndex = 0 := sorry

theorem sequential_visits (homepage : String) (urls : List String) :
  let browser := BrowserHistory.new homepage
  ∀ url ∈ urls, 
    let browser' := browser.visit url
    browser'.hashM[browser'.currIndex]! = url ∧
    browser'.currIndex = browser'.maxIndex := sorry

theorem back_navigation (homepage : String) (urls : List String) (steps : Nat) :
  let browser := BrowserHistory.new homepage
  urls.foldl (fun b url => b.visit url) browser
  |> fun b => 
    let (b', result) := b.back steps
    let expected_index := min b.maxIndex steps
    b'.currIndex = expected_index ∧ 
    result = b'.hashM[expected_index]! := sorry

theorem visit_after_back_clears_forward (homepage : String) (urls : List String) (back_steps : Nat) (new_url : String) :
  let browser := BrowserHistory.new homepage
  let browser' := urls.foldl (fun b url => b.visit url) browser
  let original_max := browser'.maxIndex
  let (browser'', _) := browser'.back back_steps
  let browser''' := browser''.visit new_url
  browser'''.maxIndex = browser'''.currIndex ∧
  (browser'''.maxIndex < original_max ∨ browser'''.maxIndex = urls.length) ∧
  browser'''.hashM[browser'''.currIndex]! = new_url := sorry

theorem forward_navigation (homepage : String) (urls : List String) (steps : Nat) :
  let browser := BrowserHistory.new homepage
  let browser' := urls.foldl (fun b url => b.visit url) browser
  let (browser'', _) := browser'.back steps
  let (browser''', result) := browser''.forward steps
  result = browser'''.hashM[browser'''.currIndex]! ∧
  browser'''.currIndex ≤ browser'''.maxIndex := sorry
-- </vc-theorems>