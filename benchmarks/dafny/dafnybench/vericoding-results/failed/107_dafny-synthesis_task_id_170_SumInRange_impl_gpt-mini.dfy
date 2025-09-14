function sumTo( a:array<int>, start:int, end:int ) : int
    requires a != null;
    requires 0 <= start && start <= end && end <= a.Length;
    decreases end;
    reads a;
    {
        if (start == end) then 0 else sumTo(a, start, end-1) + a[end-1]
    }

// <vc-helpers>
lemma SumToAppend(a: array?<int>, start: int, k: int)
  requires a != null
  requires 0 <= start && start <= k && k + 1 <= a.Length
  ensures sumTo(a, start, k + 1) == sumTo(a, start, k) + a[k]
{
  assert sumTo(a, start, k + 1) == (if start == k + 1 then 0 else sumTo(a, start, k) + a[k]);
  assert start <= k;
  assert !(start == k + 1);
  assert sumTo(a, start, k + 1) == sumTo(a, start, k) + a[k];
}
// </vc-helpers>

// <vc-spec>
method SumInRange(a: array<int>, start: int, end: int) returns (sum: int)
    requires a != null
    requires 0 <= start && start <= end && end <= a.Length
    ensures sum == sumTo(a, start, end)
// </vc-spec>
// <vc-code>
{
  var i := start;
  sum := 0;
  while i < end
    invariant start <= i && i <= end
    invariant sum == sumTo(a, start, i)
    decreases end - i
  {
    var j := i;
    sum := sum + a[j];
    i := j + 1;
    SumToAppend(a, start, j);
    assert sum == sumTo(a, start, i);
  }
}
// </vc-code>

