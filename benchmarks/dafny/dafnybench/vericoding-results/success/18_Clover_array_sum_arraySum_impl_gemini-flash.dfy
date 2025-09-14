

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method arraySum(a: array<int>, b: array<int>) returns (c: array<int> )
  requires a.Length==b.Length
  ensures c.Length==a.Length
  ensures forall i:: 0 <= i< a.Length==> a[i] + b[i]==c[i]
// </vc-spec>
// <vc-code>
{
  var n := a.Length;
  c := new int[n];
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant forall j :: 0 <= j < i ==> c[j] == a[j] + b[j]
  {
    c[i] := a[i] + b[i];
    i := i + 1;
  }
  return c;
}
// </vc-code>

