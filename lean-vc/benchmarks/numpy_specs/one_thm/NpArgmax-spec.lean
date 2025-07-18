
namespace NpArgmax

def argmax {n : Nat} (h : 0 < n) (arr : Vector Float n) : Fin n := sorry

theorem argmax_spec {n : Nat} (h : 0 < n) (arr : Vector Float n) :
  ∀ i : Fin n, i < argmax h arr → arr[argmax h arr] > arr[i]
  ∧
  ∀ i : Fin n, argmax h arr < i → arr[argmax h arr] ≥ arr[i]
  := sorry

end NpArgmax
