// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
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
  result := new int[a.Length];
  var i := 0;
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant forall j :: 0 <= j < i ==> result[j] == Cube(a[j])
  {
    result[i] := Cube(a[i]);
    i := i + 1;
  }
}
// </vc-code>
