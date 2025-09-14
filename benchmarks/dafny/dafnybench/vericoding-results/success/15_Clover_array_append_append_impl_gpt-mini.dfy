

// <vc-helpers>
// No helpers required.
// </vc-helpers>

// <vc-spec>
method append(a:array<int>, b:int) returns (c:array<int>)
  ensures  a[..] + [b] == c[..]
// </vc-spec>
// <vc-code>
{
  var n := a.Length;
  c := new int[n + 1];
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant c.Length == n + 1
    invariant forall k :: 0 <= k < i ==> c[k] == a[k]
    decreases n - i
  {
    c[i] := a[i];
    i := i + 1;
  }
  c[n] := b;
}
// </vc-code>

