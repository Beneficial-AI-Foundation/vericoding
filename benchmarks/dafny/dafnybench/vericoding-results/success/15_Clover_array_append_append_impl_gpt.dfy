

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method append(a:array<int>, b:int) returns (c:array<int>)
  ensures  a[..] + [b] == c[..]
// </vc-spec>
// <vc-code>
{
  c := new int[a.Length + 1];
  var i := 0;
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant c.Length == a.Length + 1
    invariant forall k :: 0 <= k < i ==> c[k] == a[k]
    decreases a.Length - i
  {
    c[i] := a[i];
    i := i + 1;
  }
  assert i == a.Length;
  c[a.Length] := b;

  assert c.Length == a.Length + 1;
  assert |a[..] + [b]| == a.Length + 1;

  assert forall k :: 0 <= k < a.Length ==> c[k] == a[k];
  assert c[a.Length] == b;

  assert forall k :: 0 <= k < c.Length ==> c[k] == (if k < a.Length then a[k] else b);
  assert forall k :: 0 <= k < |a[..] + [b]| ==> (a[..] + [b])[k] == (if k < a.Length then a[k] else b);
  assert forall k :: 0 <= k < c.Length ==> c[k] == (a[..] + [b])[k];

  assert a[..] + [b] == c[..];
}
// </vc-code>

