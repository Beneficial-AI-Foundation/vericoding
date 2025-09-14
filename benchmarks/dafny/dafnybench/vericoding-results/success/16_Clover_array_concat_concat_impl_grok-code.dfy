

// <vc-helpers>
// <vc-helpers>
// <vc-helpers>
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
method concat(a:array<int>, b:array<int>) returns (c:array<int>)
  ensures c.Length==b.Length+a.Length
  ensures forall k :: 0 <= k < a.Length ==> c[k] == a[k]
  ensures forall k :: 0 <= k < b.Length ==> c[k+a.Length] == b[k]
// </vc-spec>
// <vc-code>
{
  c := new int[a.Length + b.Length];
  var i := 0;
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant forall j :: 0 <= j < i ==> c[j] == a[j]
    invariant c.Length == a.Length + b.Length
  {
    c[i] := a[i];
    i := i + 1;
  }
  i := 0;
  while i < b.Length
    invariant 0 <= i <= b.Length
    invariant forall j :: 0 <= j < a.Length ==> c[j] == a[j]
    invariant forall j :: 0 <= j < i ==> c[a.Length + j] == b[j]
    invariant c.Length == a.Length + b.Length
  {
    c[a.Length + i] := b[i];
    i := i + 1;
  }
}
// </vc-code>

