

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
  c := new int[a.Length];
  for i := 0 to a.Length
    invariant forall j :: 0 <= j < i ==> c[j] == a[j] + b[j]
  {
    c[i] := a[i] + b[i];
  }
}
// </vc-code>

