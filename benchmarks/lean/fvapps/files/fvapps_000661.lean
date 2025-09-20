-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def MOD : Int := 998244353

def process_array_queries (n m : Nat) (a b : List Int) (queries : List (List Int)) : List Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem process_array_queries_result_length 
  (n m : Nat) (a b : List Int) (queries : List (List Int)) :
  queries.all (fun q => q.length > 0) →
  (process_array_queries n m a b queries).length = 
    (queries.filter (fun q => match q.head? with | some 3 => true | _ => false)).length :=
  sorry

theorem process_array_queries_result_bounds
  (n m : Nat) (a b : List Int) (queries : List (List Int)) 
  (h : queries.all (fun q => q.length > 0)) :
  (process_array_queries n m a b queries).all (fun x => 0 ≤ x ∧ x < MOD) :=
  sorry

theorem process_array_queries_symmetry 
  (n m : Nat) (a b : List Int) (queries : List (List Int))
  (h1 : queries.length > 0)
  (h2 : match (queries.get! (queries.length - 1)).head? with | some 3 => true | _ => false) :
  let swapped_queries := queries.map (fun q => match q.head? with 
    | some 1 => 2::q.tail
    | some 2 => 1::q.tail
    | _ => q)
  (process_array_queries n m a b queries).getLast! = 
  (process_array_queries m n b a swapped_queries).getLast! :=
  sorry

theorem process_array_queries_dot_product
  (a b : List Int)
  (h1 : a.length > 0)
  (h2 : b.length > 0) :
  (process_array_queries a.length b.length a b [[3]]).head! =
  (a.foldl (fun (acc : Int) (x : Int) => 
    b.foldl (fun (acc2 : Int) (y : Int) => (acc2 + ((x * y) % MOD)) % MOD) acc) 0) :=
  sorry
-- </vc-theorems>