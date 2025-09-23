-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def processes (start : String) (destination : String) (procs : List Process) : List String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem processes_returns_list (start dest : String) (procs : List Process) :
  ∀ x ∈ processes start dest procs, String.isPrefixOf "" x :=
  sorry

theorem processes_valid_path (start dest : String) (procs : List Process) 
  (h : (processes start dest procs).length > 0) :
  (List.foldl
    (fun curr step =>
      match procs.find? (fun p => p.name = step) with
      | some proc => proc.endNode
      | none => curr)
    start
    (processes start dest procs)) = dest :=
  sorry

theorem processes_same_start (s : String) (procs : List Process) :
  processes s s procs = [] :=
  sorry

theorem processes_empty_procs (start dest : String) :
  processes start dest [] = [] :=
  sorry

theorem processes_cycle_detection :
  let cycleProcs := [
    {name := "1", startNode := "a", endNode := "b"},
    {name := "2", startNode := "b", endNode := "c"},
    {name := "3", startNode := "c", endNode := "b"}]
  ; processes "a" "d" cycleProcs = [] :=
  sorry
-- </vc-theorems>