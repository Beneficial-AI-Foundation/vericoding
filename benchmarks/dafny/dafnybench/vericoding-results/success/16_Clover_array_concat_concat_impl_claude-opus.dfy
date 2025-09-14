

// <vc-helpers>

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
    invariant forall k :: 0 <= k < i ==> c[k] == a[k]
  {
    c[i] := a[i];
    i := i + 1;
  }
  var j := 0;
  while j < b.Length
    invariant 0 <= j <= b.Length
    invariant forall k :: 0 <= k < a.Length ==> c[k] == a[k]
    invariant forall k :: 0 <= k < j ==> c[k + a.Length] == b[k]
  {
    c[a.Length + j] := b[j];
    j := j + 1;
  }
}
// </vc-code>

