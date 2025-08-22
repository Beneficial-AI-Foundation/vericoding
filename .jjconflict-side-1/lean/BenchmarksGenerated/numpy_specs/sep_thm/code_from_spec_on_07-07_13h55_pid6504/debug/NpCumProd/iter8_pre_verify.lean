/-
# Cumulative Product Specification

Port of np_cum_prod.dfy to Lean 4
-/

namespace DafnySpecs.NpCumProd

-- LLM HELPER
def cumProdAux {n : Nat} (a : Vector Int n) : Nat → Int
  | 0 => if h : 0 < n then a[0]'(by omega) else 0
  | k + 1 => if h : k + 1 < n then cumProdAux a k * a[k + 1]'h else 0

/-- Cumulative product operation on a vector of integers -/
def cumProd {n : Nat} (a : Vector Int n) : Vector Int n := 
  Vector.ofFn (fun i => cumProdAux a i.val)

-- LLM HELPER
lemma cumProdAux_zero {n : Nat} (a : Vector Int n) (hn : 0 < n) :
    cumProdAux a 0 = a[0]'(by omega) := by
  simp [cumProdAux, hn]

-- LLM HELPER
lemma cumProdAux_succ {n : Nat} (a : Vector Int n) (k : Nat) (hk : k + 1 < n) :
    cumProdAux a (k + 1) = cumProdAux a k * a[k + 1]'hk := by
  simp [cumProdAux, hk]

-- LLM HELPER
lemma cumProd_get {n : Nat} (a : Vector Int n) (i : Fin n) :
    (cumProd a)[i] = cumProdAux a i.val := by
  simp [cumProd, Vector.get_ofFn]

/-- The cumulative product preserves the first element -/
theorem cumProd_first {n : Nat} (hn : 0 < n) (a : Vector Int n) :
    (cumProd a)[0]'(by omega) = a[0]'(by omega) := by
  rw [cumProd_get]
  simp [cumProdAux_zero a hn]

/-- Each element is the product of the previous cumulative product and the current element -/
theorem cumProd_recursive {n : Nat} (a : Vector Int n) (i : Fin n) (hi : 0 < i.val) :
    (cumProd a)[i] = (cumProd a)[i.val - 1]'(by omega) * a[i] := by
  rw [cumProd_get, cumProd_get]
  have h1 : i.val - 1 + 1 = i.val := Nat.sub_add_cancel hi
  rw [← h1]
  rw [cumProdAux_succ]
  · congr 1
    rw [h1]
  · rw [h1]
    exact i.isLt

end DafnySpecs.NpCumProd