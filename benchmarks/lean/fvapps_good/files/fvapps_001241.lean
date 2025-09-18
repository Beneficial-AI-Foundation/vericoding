-- <vc-preamble>
def isValidMatrix (matrix : List (List Int)) : Bool :=
  match matrix with
  | [] => false
  | x::xs => let n := x.length
             matrix.length = n && matrix.all (fun row => row.length = n)
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def findMaxTrace (matrix : List (List Int)) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem max_trace_geq_main_diagonal (matrix : List (List Int)) 
  (h : isValidMatrix matrix = true) : 
  findMaxTrace matrix ≥ 
    (List.range matrix.length).foldl 
      (fun acc i => acc + (matrix.get! i).get! i) 0 :=
sorry

theorem max_trace_geq_max_element (matrix : List (List Int)) 
  (h : isValidMatrix matrix = true) :
  findMaxTrace matrix ≥ 
    (matrix.map (List.foldl max 0)).foldl max 0 :=
sorry

theorem constant_matrix_trace (n : Nat) (h : n > 0) :
  let matrix := List.replicate n (List.replicate n 1)
  findMaxTrace matrix = n :=
sorry

theorem identity_matrix_trace (n : Nat) (h : n > 0) :
  let matrix := List.range n |> List.map (fun i => 
    List.range n |> List.map (fun j => if i = j then 1 else 0))
  findMaxTrace matrix = n :=
sorry

theorem empty_matrix_error : 
  isValidMatrix [] = false :=
sorry
-- </vc-theorems>