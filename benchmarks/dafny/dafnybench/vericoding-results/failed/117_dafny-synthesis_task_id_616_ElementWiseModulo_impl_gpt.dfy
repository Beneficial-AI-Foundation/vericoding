

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method ElementWiseModulo(a: array<int>, b: array<int>) returns (result: array<int>)
    requires a != null && b != null
    requires a.Length == b.Length
    requires forall i :: 0 <= i < b.Length ==> b[i] != 0
    ensures result != null
    ensures result.Length == a.Length
    ensures forall i :: 0 <= i < result.Length ==> result[i] == a[i] % b[i]
// </vc-spec>
// <vc-code>
{
  var n := a.Length;
  result := new int[n];
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant n == a.Length
    invariant n == b.Length
    invariant result.Length == n
    invariant forall j :: 0 <= j < i ==> result[j] == a[j] % b[j]
    decreases n - i
  {
    assert 0 <= i < a.Length;
    assert 0 <= i < b.Length;
    assert b[i] != 0;
    result[i] := a[i] % b[i];
    i := i + 1;
  }
}
// </vc-code>

