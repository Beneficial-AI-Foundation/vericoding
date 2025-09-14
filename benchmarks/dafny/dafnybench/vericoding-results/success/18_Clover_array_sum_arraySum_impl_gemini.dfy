// <vc-preamble>
// </vc-preamble>

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
  var i := 0;
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant c.Length == a.Length
    invariant forall k :: 0 <= k < i ==> c[k] == a[k] + b[k]
  {
    c[i] := a[i] + b[i];
    i := i + 1;
  }
}
// </vc-code>
