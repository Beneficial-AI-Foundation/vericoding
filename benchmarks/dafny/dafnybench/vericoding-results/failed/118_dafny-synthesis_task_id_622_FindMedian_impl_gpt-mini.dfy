

// <vc-helpers>
lemma SuppressWarnings() {}

lemma EvenIndexBounds(n: int)
  requires n > 0
  requires n % 2 == 0
  ensures 0 <= n / 2 - 1
  ensures n / 2 - 1 < n
  ensures 0 <= n / 2 < n
{
  var m := n / 2;
  // n == 2*m + n%2 is a general property of division/modulo
  assert n == 2*m + n % 2;
  assert n % 2 == 0;
  assert n == 2*m;
  // From n == 2*m and n > 0 we get m > 0
  assert m > 0;
  assert 0 <= m - 1;
  assert m - 1 < n;
  assert 0 <= m;
  assert m < n;
}
// </vc-helpers>

// <vc-spec>
method FindMedian(a: array<int>, b: array<int>) returns (median: int)
    requires a != null && b != null
    requires a.Length == b.Length
    requires a.Length > 0
    requires forall i :: 0 <= i < a.Length - 1 ==> a[i] <= a[i + 1]
    requires forall i :: 0 <= i < b.Length - 1 ==> b[i] <= b[i + 1]
    ensures median == if (a.Length % 2 == 0) then (a[a.Length / 2 - 1] + b[0]) / 2 else a[a.Length / 2]
// </vc-spec>
// <vc-code>
{
  // Re-assert the given preconditions to aid verification of the body.
  assert a.Length == b.Length;
  assert a.Length > 0;
  if a.Length % 2 == 0 {
    EvenIndexBounds(a.Length);
    var i := a.Length / 2 - 1;
    var j := a.Length / 2;
    assert 0 <= i < a.Length;
    assert 0 <= j < a.Length;
    // b[0] is valid because b.Length == a.Length and a.Length > 0
    median := (a[i] + b[0]) / 2;
  } else {
    var k := a.Length / 2;
    assert 0 <= k < a.Length;
    median := a[k];
  }
}
// </vc-code>

