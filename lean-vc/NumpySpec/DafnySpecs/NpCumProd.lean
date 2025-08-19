/-
# Cumulative Product Specification

Port of np_cum_prod.dfy to Lean 4
-/

namespace DafnySpecs.NpCumProd

/-- Cumulative product operation on a vector of integers -/
def cumProd {n : Nat} (a : Vector Int n) : Vector Int n := sorry

/-- The cumulative product preserves the first element -/
theorem cumProd_first {n : Nat} (hn : 0 < n) (a : Vector Int n) :
    (cumProd a)[0]'(by omega) = a[0]'(by omega) := sorry

/-- Each element is the product of the previous cumulative product and the current element -/
theorem cumProd_recursive {n : Nat} (a : Vector Int n) (i : Fin n) (hi : 0 < i.val) :
    (cumProd a)[i] = (cumProd a)[i.val - 1]'(by omega) * a[i] := sorry

end DafnySpecs.NpCumProd