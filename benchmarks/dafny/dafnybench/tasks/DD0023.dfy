// <vc-preamble>
predicate sorted(a:array<int>, from:int, to:int)
  requires a != null;
  reads a; 
  requires 0 <= from <= to <= a.Length;
{
  forall x, y :: from <= x < y < to ==> a[x] <= a[y]
}

predicate pivot(a:array<int>, to:int, pvt:int)
  requires a != null;
  reads a;
  requires 0 <= pvt < to <= a.Length;
{
  forall x, y :: 0 <= x < pvt < y < to ==> a[x] <= a[y]
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method BubbleSort (a: array<int>)
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
