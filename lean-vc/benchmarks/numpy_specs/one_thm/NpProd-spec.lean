namespace NpProd

def prod {n : Nat} (a : Vector Int n) : Int := sorry

def prodArray {n : Nat} (a : Vector Int n) (start finish : Nat) : Int := sorry

theorem prod_spec {n : Nat} (a : Vector Int n) :
  prod a = prodArray a 0 n ∧
  ∀ start finish : Nat, start ≤ finish → finish ≤ n → 
    prodArray a start finish = (List.range (finish - start)).foldl (fun acc i => acc * a[start + i]'sorry) 1 ∧
  ∀ m n : Nat, ∀ a : Vector Int m, ∀ b : Vector Int n, prod (a ++ b) = prod a * prod b ∧
  ∀ i : Fin n, a[i] = 0 → prod a = 0 := sorry

end NpProd 