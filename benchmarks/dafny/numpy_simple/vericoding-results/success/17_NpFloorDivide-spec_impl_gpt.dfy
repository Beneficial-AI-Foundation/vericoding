// <vc-preamble>
predicate IsNonZeroVector(v: seq<int>)
{
    forall i :: 0 <= i < |v| ==> v[i] != 0
}
// </vc-preamble>

// <vc-helpers>
lemma NonZeroFromVector(b: array<int>, i: int)
    requires 0 <= i < b.Length
    requires IsNonZeroVector(b[..])
    ensures b[i] != 0
{
    assert |b[..]| == b.Length;
    assert 0 <= i < |b[..]|;
    assert b[..][i] != 0;
    assert b[..][i] == b[i];
}
// </vc-helpers>

// <vc-spec>
method FloorDivide(a: array<int>, b: array<int>) returns (result: array<int>)
    requires a.Length == b.Length
    requires IsNonZeroVector(b[..])
    ensures result.Length == a.Length
    ensures forall i :: 0 <= i < result.Length ==> result[i] == a[i] / b[i]
// </vc-spec>
// <vc-code>
{
  var n := a.Length;
  result := new int[n];
  var i := 0;
  assert n == b.Length;
  while i < n
    invariant 0 <= i <= n
    invariant result.Length == n
    invariant n == a.Length
    invariant n == b.Length
    invariant IsNonZeroVector(b[..])
    invariant forall j :: 0 <= j < i ==> result[j] == a[j] / b[j]
  {
    NonZeroFromVector(b, i);
    result[i] := a[i] / b[i];
    i := i + 1;
  }
}
// </vc-code>
