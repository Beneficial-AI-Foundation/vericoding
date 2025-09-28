// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): consistent cube helper for reuse */
function cube(x: int): int { x * x * x }
// </vc-helpers>

// <vc-spec>
method CubeElements(a: array<int>) returns (result: array<int>)
    ensures
        result.Length == a.Length &&
        forall i :: 0 <= i < a.Length ==> result[i] == a[i] * a[i] * a[i]
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): Implement loop without redundant non-null invariant */
  result := new int[a.Length];
  var i := 0;
  while i < a.Length
    invariant result.Length == a.Length
    invariant 0 <= i <= a.Length
    invariant forall j :: 0 <= j < i ==> result[j] == a[j] * a[j] * a[j]
  {
    result[i] := a[i] * a[i] * a[i];
    i := i + 1;
  }
}
// </vc-code>
