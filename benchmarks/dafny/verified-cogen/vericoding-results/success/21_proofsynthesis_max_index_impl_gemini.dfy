// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
predicate is_max_in_prefix(a: array<int>, max_idx: int, limit: int)
  reads a
  requires 0 < limit <= a.Length
  requires 0 <= max_idx < limit
{
  forall k :: 0 <= k < limit ==> a[max_idx] >= a[k]
}
// </vc-helpers>

// <vc-spec>
method MyFun1(x: array<int>) returns (max_index: int)
    requires x.Length >= 1
    ensures 0 <= max_index < x.Length
    ensures forall k :: 0 <= k < x.Length ==> x[max_index] >= x[k]
// </vc-spec>
// <vc-code>
{
  max_index := 0;
  var i := 1;
  while i < x.Length
    invariant 1 <= i <= x.Length
    invariant 0 <= max_index < i
    invariant is_max_in_prefix(x, max_index, i)
  {
    if x[i] > x[max_index] {
      max_index := i;
    }
    i := i + 1;
  }
}
// </vc-code>
