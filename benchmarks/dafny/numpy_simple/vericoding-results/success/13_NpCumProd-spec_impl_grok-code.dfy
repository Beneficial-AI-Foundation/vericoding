// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method CumProd(a: array<int>) returns (result: array<int>)
    requires a.Length > 0
    ensures 
        result.Length == a.Length &&
        result[0] == a[0] &&
        forall i :: 0 < i < a.Length ==> result[i] == result[i-1] * a[i]
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): Fixed variable name conflict for result */
  var cumProd := new int[a.Length];
  cumProd[0] := a[0];
  var i := 1;
  while i < a.Length
    invariant 1 <= i <= a.Length
    invariant cumProd[0] == a[0]
    invariant forall k :: 0 < k < i ==> cumProd[k] == cumProd[k-1] * a[k]
  {
    cumProd[i] := cumProd[i-1] * a[i];
    i := i + 1;
  }
  result := cumProd;
}
// </vc-code>
