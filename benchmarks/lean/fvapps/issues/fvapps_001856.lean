-- <vc-preamble>
def birth (t : ThroneInheritance) (parent child : String) : ThroneInheritance := sorry

def death (t : ThroneInheritance) (name : String) : ThroneInheritance := sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def getInheritanceOrder (t : ThroneInheritance) : List String := sorry

theorem new_kingdom_order (kingName : String) :
  getInheritanceOrder ⟨kingName⟩ = [kingName] := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem single_birth_order (kingName childName : String) (h : kingName ≠ childName) :
  let t := birth ⟨kingName⟩ kingName childName
  getInheritanceOrder t = [kingName, childName] := sorry

theorem multiple_children_order (kingName : String) (children : List String) 
  (h1 : children.length > 0)
  (h2 : ∀ c ∈ children, kingName ≠ c)
  (h3 : List.Nodup children) :
  let init := ⟨kingName⟩
  let final := children.foldl (fun t c => birth t kingName c) init
  getInheritanceOrder final = kingName :: children := sorry

theorem death_removes_from_order (kingName childName : String) (h : kingName ≠ childName) :
  let t1 := birth ⟨kingName⟩ kingName childName
  let t2 := death t1 childName
  getInheritanceOrder t2 = [kingName] := sorry

theorem deaths_and_births (kingName : String) (children deaths : List String)
  (h1 : children.length > 0)
  (h2 : deaths.length ≤ 2)
  (h3 : ∀ c ∈ children, kingName ≠ c)  
  (h4 : List.Nodup children) :
  let init := ⟨kingName⟩
  let afterBirths := children.foldl (fun t c => birth t kingName c) init
  let final := deaths.foldl (fun t d => death t d) afterBirths
  let order := getInheritanceOrder final
  (kingName ∉ deaths → kingName ∈ order) ∧
  (∀ c ∈ children, c ∉ deaths → c ∈ order) ∧
  (∀ c ∈ children, c ∈ deaths → c ∉ order) := sorry
-- </vc-theorems>