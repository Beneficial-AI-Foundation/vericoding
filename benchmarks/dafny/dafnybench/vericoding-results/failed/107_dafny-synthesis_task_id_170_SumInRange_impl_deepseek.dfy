function sumTo( a:array<int>, start:int, end:int ) : int
    requires a != null;
    requires 0 <= start && start <= end && end <= a.Length;
    decreases end;
    reads a;
    {
        if (start == end) then 0 else sumTo(a, start, end-1) + a[end-1]
    }

// <vc-helpers>
lemma sumToRecursiveLemma(a: array<int>, start: int, end: int)
  requires 0 <= start && start <= end && end <= a.Length
  ensures sumTo(a, start, end) == 
    (if start < end then sumTo(a, start, end - 1) + a[end - 1] else 0)
{
}

lemma sumToEmptyRange(a: array<int>, i: int)
  requires 0 <= i <= a.Length
  ensures sumTo(a, i, i) == 0
{
}

lemma sumToStep(a: array<int>, i: int, j: int)
  requires 0 <= i < j <= a.Length
  ensures sumTo(a, i, j) == sumTo(a, i, j-1) + a[j-1]
{
}

lemma sumToMonotonic(a: array<int>, start: int, mid: int, end: int)
  requires 0 <= start <= mid <= end <= a.Length
  ensures sumTo(a, start, end) == sumTo(a, start, mid) + sumTo(a, mid, end)
{
  if mid < end {
    sumToMonotonic(a, start, mid, end - 1);
    sumToStep(a, mid, end);
    assert sumTo(a, start, end) == sumTo(a, start, end - 1) + a[end - 1];
    assert sumTo(a, start, end - 1) == sumTo(a, start, mid) + sumTo(a, mid, end - 1);
    assert sumTo(a, mid, end) == sumTo(a, mid, end - 1) + a[end - 1];
    assert sumTo(a, start, end) == sumTo(a, start, mid) + sumTo(a, mid, end);
  }
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
  sum := 0;
  var i := start;
  while i < end
    invariant start <= i <= end
    invariant sum == sumTo(a, start, i)
  {
    sum := sum + a[i];
    i := i + 1;
    sumToStep(a, start, i);
    assert sumTo(a, start, i) == sumTo(a, start, i-1) + a[i-1];
    assert sum == sumTo(a, start, i);
  }
}
// </vc-code>

