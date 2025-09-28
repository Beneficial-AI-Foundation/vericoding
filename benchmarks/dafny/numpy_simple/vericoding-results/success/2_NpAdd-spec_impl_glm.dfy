// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method Add(a: array<int>, b: array<int>) returns (result: array<int>)
    requires a.Length == b.Length
    ensures 
        result.Length == a.Length &&
        forall i :: 0 <= i < result.Length ==> result[i] == a[i] + b[i]
// </vc-spec>
// <vc-code>
{
  result := new int[a.Length];
  for i := 0 to a.Length
      invariant forall j :: 0 <= j < i ==> result[j] == a[j] + b[j]
  {
      result[i] := a[i] + b[i];
  }
}
// </vc-code>
