// <vc-preamble>
function sumTo( a:array<int>, start:int, end:int ) : int
    requires a != null;
    requires 0 <= start && start <= end && end <= a.Length;
    decreases end;
    reads a;
    {
        if (start == end) then 0 else sumTo(a, start, end-1) + a[end-1]
    }
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): kept correct lemma for loop invariant */
lemma SumToUnfold(a: array<int>, start: int, i: int)
  requires 0 <= start <= i < a.Length
  ensures sumTo(a, start, i + 1) == sumTo(a, start, i) + a[i]
{
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
  /* code modified by LLM (iteration 5): removed semicolons to fix compilation warnings */
  sum := 0
  var i := start
  while i < end
    invariant 0 <= start <= i <= end
    invariant sum == sumTo(a, start, i)
    decreases end - i
  {
    SumToUnfold(a, start, i)
    sum := sum + a[i]
    i := i + 1
  }
}
// </vc-code>
