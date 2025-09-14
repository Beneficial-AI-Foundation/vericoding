

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method appendArray(a: array<int>, b: array<int>) returns (c: array<int>)
ensures c.Length == a.Length + b.Length
ensures forall i :: 0 <= i < a.Length ==> a[i] == c[i]
ensures forall i :: 0 <= i < b.Length ==> b[i] == c[a.Length + i]
// </vc-spec>
// <vc-code>
{
  var n := a.Length;
  var m := b.Length;
  c := new int[n + m];
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant c.Length == n + m
    invariant forall k :: 0 <= k < i ==> c[k] == a[k]
    decreases n - i
  {
    c[i] := a[i];
    i := i + 1;
  }
  var j := 0;
  while j < m
    invariant 0 <= j <= m
    invariant c.Length == n + m
    invariant forall k :: 0 <= k < n ==> c[k] == a[k]
    invariant forall k :: 0 <= k < j ==> c[n + k] == b[k]
    decreases m - j
  {
    c[n + j] := b[j];
    j := j + 1;
  }
}
// </vc-code>

