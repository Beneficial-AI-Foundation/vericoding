

// <vc-helpers>
lemma NoIndexHasElemImpliesNotIn(a: array<char>, c: char, n: nat)
  requires n <= a.Length
  requires forall i | 0 <= i < n :: a[i] != c
  ensures c !in a[..n]
{
  assert !(c in a[..n]) by {
    if c in a[..n] {
      var k: int :| 0 <= k < |a[..n]| && a[..n][k] == c;
      assert |a[..n]| == n;
      assert 0 <= k < n;
      assert a[..n][k] == c;
      assert a[..n][k] == a[k];
      assert a[k] != c;
      assert false;
    }
  }
}
// </vc-helpers>

// <vc-spec>
method firstE(a: array<char>) returns (x: int)
ensures if 'e' in a[..] then 0 <= x < a.Length && a[x] == 'e' && forall i | 0 <= i < x :: a[i] != 'e' else x == -1
// </vc-spec>
// <vc-code>
{
  var i := 0;
  while i < a.Length && a[i] != 'e'
    invariant 0 <= i <= a.Length
    invariant forall j :: 0 <= j < i ==> a[j] != 'e'
    decreases a.Length - i
  {
    i := i + 1;
  }
  if i < a.Length {
    x := i;
  } else {
    x := -1;
    NoIndexHasElemImpliesNotIn(a, 'e', i);
    assert i == a.Length;
    assert a[..i] == a[..];
    assert !('e' in a[..]);
  }
}
// </vc-code>

