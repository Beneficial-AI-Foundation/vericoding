

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
  c := new int[a.Length + b.Length];
  var i := 0;
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant c.Length == a.Length + b.Length
    invariant forall k :: 0 <= k < i ==> c[k] == a[k]
  {
    c[i] := a[i];
    i := i + 1;
  }
  assert i == a.Length;
  assert forall k :: 0 <= k < a.Length ==> c[k] == a[k];
  i := 0;
  while i < b.Length
    invariant 0 <= i <= b.Length
    invariant c.Length == a.Length + b.Length
    invariant forall k :: 0 <= k < a.Length ==> c[k] == a[k]
    invariant forall k :: 0 <= k < i ==> c[a.Length + k] == b[k]
  {
    c[a.Length + i] := b[i];
    i := i + 1;
  }
}
// </vc-code>

