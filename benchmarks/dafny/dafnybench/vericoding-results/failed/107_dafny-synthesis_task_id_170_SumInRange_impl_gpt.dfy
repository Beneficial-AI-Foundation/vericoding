function sumTo( a:array<int>, start:int, end:int ) : int
    requires a != null;
    requires 0 <= start && start <= end && end <= a.Length;
    decreases end;
    reads a;
    {
        if (start == end) then 0 else sumTo(a, start, end-1) + a[end-1]
    }

// <vc-helpers>
lemma SumToStep(a: array<int>, start: int, end: int)
  requires 0 <= start && start < end && end <= a.Length
  ensures sumTo(a, start, end) == sumTo(a, start, end - 1) + a[end - 1]
{
  assert sumTo(a, start, end) ==
    (if start == end then 0 else sumTo(a, start, end - 1) + a[end - 1]);
  assert start != end;
  assert sumTo(a, start, end) == sumTo(a, start, end - 1) + a[end - 1];
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

  assert sumTo(a, start, i) == 0 by {
    assert i == start;
    assert sumTo(a, start, start) == 0;
  }
  assert sum == sumTo(a, start, i);

  while i < end
    invariant 0 <= start && start <= i && i <= end && end <= a.Length
    invariant sum == sumTo(a, start, i)
    decreases end - i
  {
    assert 0 <= i && i < a.Length;
    assert sumTo(a, start, i + 1) == sumTo(a, start, i) + a[i] by {
      SumToStep(a, start, i + 1);
    }
    sum := sum + a[i];
    i := i + 1;
  }
}
// </vc-code>

