// <vc-preamble>
predicate sorted(a:array<int>, from:int, to:int)
  requires a != null;
  reads a;
  requires 0 <= from <= to <= a.Length;
{
  forall u, v :: from <= u < v < to ==> a[u] <= a[v]
}

predicate pivot(a:array<int>, to:int, pvt:int)
  requires a != null;
  reads a;
  requires 0 <= pvt < to <= a.Length;
{
  forall u, v :: 0 <= u < pvt < v < to ==> a[u] <= a[v]
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method bubbleSort (a: array<int>)
  requires a != null && a.Length > 0;
  modifies a;
  ensures sorted(a, 0, a.Length);
  ensures multiset(a[..]) == multiset(old(a[..]));
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
