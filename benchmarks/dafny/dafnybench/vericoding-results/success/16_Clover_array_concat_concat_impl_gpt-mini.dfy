

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
  var total := a.Length + b.Length;
  c := new int[total];
  var k := 0;
  while k < total
    invariant 0 <= k <= total
    invariant forall t :: 0 <= t < k && t < a.Length ==> c[t] == a[t]
    invariant forall t :: 0 <= t < k && t >= a.Length ==> c[t] == b[t - a.Length]
  {
    if k < a.Length {
      c[k] := a[k];
    } else {
      c[k] := b[k - a.Length];
    }
    k := k + 1;
  }
}
// </vc-code>

