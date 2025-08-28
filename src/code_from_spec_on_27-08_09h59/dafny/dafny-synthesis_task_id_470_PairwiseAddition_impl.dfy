// <vc-helpers>
// </vc-helpers>

// <vc-spec>
// <vc-spec>
method PairwiseAddition(a: array<int>) returns (result: array<int>)
    requires a != null
    requires a.Length % 2 == 0
    ensures result != null
    ensures result.Length == a.Length / 2
    ensures forall i :: 0 <= i < result.Length ==> result[i] == a[2*i] + a[2*i + 1]
// </vc-spec>
// </vc-spec>

// <vc-code>
{
  var n := a.Length / 2;
  result := new int[n];
  
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant forall j :: 0 <= j < i ==> result[j] == a[2*j] + a[2*j + 1]
  {
    result[i] := a[2*i] + a[2*i + 1];
    i := i + 1;
  }
}
// </vc-code>
