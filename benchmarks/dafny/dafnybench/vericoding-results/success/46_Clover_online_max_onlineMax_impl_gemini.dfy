// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function max_prefix(a: array<int>, n: int): int
  requires 0 < n <= a.Length
  reads a
  ensures exists i :: 0 <= i < n && max_prefix(a, n) == a[i]
  ensures forall i :: 0 <= i < n ==> a[i] <= max_prefix(a, n)
{
  if n == 1 then a[0]
  else
    var m_prev := max_prefix(a, n - 1);
    if m_prev < a[n-1] then a[n-1] else m_prev
}
// </vc-helpers>

// <vc-spec>
method onlineMax(a: array<int>, x: int) returns (ghost m:int, p:int)
  requires 1<=x<a.Length
  requires a.Length!=0
  ensures x<=p<a.Length
  ensures forall i::0<=i<x==> a[i]<=m
  ensures exists i::0<=i<x && a[i]==m
  ensures x<=p<a.Length-1 ==> (forall i::0<=i<p ==> a[i]<a[p])
  ensures (forall i::x<=i<a.Length && a[i]<=m) ==> p==a.Length-1
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): fixed ghost variable usage in control flow */
  m := max_prefix(a, x);
  var real_m := max_prefix(a, x);
  p := x;
  while p < a.Length - 1 && a[p] <= real_m
    invariant x <= p < a.Length
    invariant real_m == max_prefix(a, x)
    invariant forall i :: x <= i < p ==> a[i] <= real_m
    decreases a.Length - p
  {
    p := p + 1;
  }
}
// </vc-code>
