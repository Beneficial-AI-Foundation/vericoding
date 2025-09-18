// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): simple cube function */
function Cube(x: int): int { x * x * x }
// </vc-helpers>

// <vc-spec>
method CubeElements(a: array<int>) returns (result: array<int>)
    ensures
        result.Length == a.Length &&
        forall i :: 0 <= i < a.Length ==> result[i] == a[i] * a[i] * a[i]
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): implemented loop to fill result with cubes and removed redundant null-check invariant */
  result := new int[a.Length];
  var i := 0;
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant result.Length == a.Length
    invariant forall k :: 0 <= k < i ==> result[k] == a[k] * a[k] * a[k]
    decreases a.Length - i
  {
    result[i] := Cube(a[i]);
    i := i + 1;
  }
}
// </vc-code>
