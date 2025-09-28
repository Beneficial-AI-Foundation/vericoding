// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): removed null checks to avoid warnings and kept only length equality */
predicate SameLength(a: array<int>, b: array<int>) { a.Length == b.Length }
// </vc-helpers>

// <vc-spec>
method ArrayProduct(a: array<int>, b: array<int>) returns (result: array<int>)
    requires a.Length == b.Length
    ensures result.Length == a.Length
    ensures forall i :: 0 <= i < a.Length ==> result[i] == a[i] * b[i]
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): implemented array-wise product with loop invariants */
  result := new int[a.Length];
  var i := 0;
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant result.Length == a.Length
    invariant forall j :: 0 <= j < i ==> result[j] == a[j] * b[j]
    decreases a.Length - i
  {
    result[i] := a[i] * b[i];
    i := i + 1;
  }
}
// </vc-code>
