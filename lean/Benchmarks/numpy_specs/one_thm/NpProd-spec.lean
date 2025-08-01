namespace NpProd

def prod {n : Nat} (a : Vector Int n) : Int := sorry

def prodArray {n : Nat} (a : Vector Int n) (start finish : Nat) : Int := sorry

theorem prod_spec {n : Nat} (a : Vector Int n) :
  prod a = prodArray a 0 n ∧
  (∀ i : Fin n, a[i] = 0 → prod a = 0) := sorry

end NpProd 