// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
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
  result := new int[a.Length];
  var index := 0;
  while index < a.Length
    invariant index <= a.Length
    invariant forall j :: 0 <= j < index ==> result[j] == a[j] * a[j] * a[j]
  {
    result[index] := a[index] * a[index] * a[index];
    index := index + 1;
  }
}
// </vc-code>
