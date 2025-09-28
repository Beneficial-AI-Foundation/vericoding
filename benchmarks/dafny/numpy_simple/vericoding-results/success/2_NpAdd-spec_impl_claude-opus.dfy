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
  var i := 0;
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant forall j :: 0 <= j < i ==> result[j] == a[j] + b[j]
  {
    result[i] := a[i] + b[i];
    i := i + 1;
  }
}
// </vc-code>
