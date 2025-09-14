function sumTo( a:array<int>, start:int, end:int ) : int
    requires a != null;
    requires 0 <= start && start <= end && end <= a.Length;
    decreases end;
    reads a;
    {
        if (start == end) then 0 else sumTo(a, start, end-1) + a[end-1]
    }

// <vc-helpers>
function sumTo(a: array?<int>, start: int, end: int): int
    requires a != null
    requires 0 <= start && start <= end && end <= a.Length
    decreases end
    reads a
    {
        if (start == end) then 0 else sumTo(a, start, end-1) + a[end-1]
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
  while (i < end)
    invariant 0 <= start <= i <= end <= a.Length
    invariant sum == sumTo(a, start, i)
    decreases end - i
  {
    sum := sum + a[i];
    i := i + 1;
  }
}
// </vc-code>

