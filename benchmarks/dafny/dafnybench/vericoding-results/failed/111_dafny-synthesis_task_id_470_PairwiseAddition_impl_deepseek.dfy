

// <vc-helpers>
lemma EvenArrayLemma(a: array<int>)
  requires a != null
  requires a.Length % 2 == 0
  ensures a.Length >= 0
  ensures a.Length / 2 >= 0
{
}
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
method PairwiseAddition(a: array<int>) returns (result: array<int>)
    requires a != null
    requires a.Length % 2 == 0
    ensures result != null
    ensures result.Length == a.Length / 2
    ensures forall i :: 0 <= i < result.Length ==> result[i] == a[2*i] + a[2*i + 1]
// </vc-spec>
// <vc-code>
{
  var n := a.Length;
  result := new int[n / 2];
  var i := 0;
  var j := 0;
  
  while i < n
    invariant 0 <= i <= n
    invariant i % 2 == 0
    invariant 0 <= j <= n / 2
    invariant j == i / 2
    invariant forall k :: 0 <= k < j ==> result[k] == a[2*k] + a[2*k + 1]
  {
    result[j] := a[i] + a[i + 1];
    i := i + 2;
    j := j + 1;
  }
}
// </vc-code>

