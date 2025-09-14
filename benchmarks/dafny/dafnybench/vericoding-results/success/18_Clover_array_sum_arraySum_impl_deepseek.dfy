

// <vc-helpers>
lemma {:induction false} ArraySumLemma(a: array<int>, b: array<int>, c: array<int>, n: int)
  requires a.Length == b.Length && c.Length == a.Length
  requires 0 <= n <= a.Length
  requires forall i :: 0 <= i < n ==> a[i] + b[i] == c[i]
  ensures forall i :: 0 <= i < n ==> a[i] + b[i] == c[i]
{
}
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
    invariant forall j :: 0 <= j < i ==> a[j] + b[j] == c[j]
  {
    c[i] := a[i] + b[i];
    i := i + 1;
  }
}
// </vc-code>

