// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method CumSum(a: array<int>) returns (result: array<int>)
    requires a.Length > 0
    ensures 
        result.Length == a.Length &&
        result[0] == a[0] &&
        forall i :: 1 <= i < a.Length ==> result[i] == result[i - 1] + a[i]
// </vc-spec>
// <vc-code>
{
  result := new int[a.Length];
  result[0] := a[0];
  var i := 1;
  while i < a.Length
    invariant 1 <= i <= a.Length
    invariant result[0] == a[0]
    invariant forall j :: 1 <= j < i ==> result[j] == result[j - 1] + a[j]
  {
    result[i] := result[i - 1] + a[i];
    i := i + 1;
  }
}
// </vc-code>
