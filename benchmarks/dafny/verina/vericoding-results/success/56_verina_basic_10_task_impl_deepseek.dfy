// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function AllIndicesLessThan(n: int, a: array<int>, idx: int): bool
  requires 0 <= idx <= a.Length
  reads a
  decreases a.Length - idx
{
  if idx == a.Length then
    true
  else
    n > a[idx] && AllIndicesLessThan(n, a, idx + 1)
}

/* helper modified by LLM (iteration 5): Remove reads clause from lemma */
lemma AllIndicesLessThanEquivalence(n: int, a: array<int>, idx: int)
  requires 0 <= idx <= a.Length
  ensures AllIndicesLessThan(n, a, idx) == (forall i :: idx <= i < a.Length ==> n > a[i])
  decreases a.Length - idx
{
  if idx < a.Length {
    AllIndicesLessThanEquivalence(n, a, idx + 1);
  }
}
// </vc-helpers>

// <vc-spec>
method IsGreater(n: int, a: array<int>) returns (result: bool)
    requires a.Length > 0
    ensures result == (forall i :: 0 <= i < a.Length ==> n > a[i])
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): Call helper functions with proper verification */
  result := AllIndicesLessThan(n, a, 0);
  AllIndicesLessThanEquivalence(n, a, 0);
}
// </vc-code>
