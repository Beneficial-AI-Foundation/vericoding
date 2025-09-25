-- <vc-preamble>
def dirList := List Dir

def getEndpoint (path : dirList) : Int × Int := sorry

def simplify (path : dirList) : dirList := sorry 

theorem simplify_same_endpoint (path : dirList) : 
  getEndpoint path = getEndpoint (simplify path) := sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def isValidDir (d : Dir) : Bool := sorry

theorem simplify_valid_chars (path : dirList) (d : Dir) :
  List.elem d (simplify path) → isValidDir d := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem simplify_shorter (path : dirList) :
  (simplify path).length ≤ path.length := sorry

theorem simplify_empty (path : dirList) :
  path = [] → simplify path = [] := sorry

theorem simplify_idempotent (path : dirList) :
  simplify (simplify path) = simplify path := sorry

/-
info: '>'
-/
-- #guard_msgs in
-- #eval simplify "<>>"

/-
info: '<^^^^'
-/
-- #guard_msgs in
-- #eval simplify "<^^>v<^^^"

/-
info: ''
-/
-- #guard_msgs in
-- #eval simplify ""
-- </vc-theorems>