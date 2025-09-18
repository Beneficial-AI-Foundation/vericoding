// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

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
  var i: nat := 0;
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant result.Length == a.Length
    invariant forall k :: 0 <= k < i ==> result[k] == a[k]*a[k]*a[k]
  {
    result[i] := a[i]*a[i]*a[i];
    i := i + 1;
  }
}
// </vc-code>
