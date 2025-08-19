//ATOM
/* code modified by LLM (iteration 1): removed redundant null check since array<int> is non-null */
function sumTo( a:array<int>, start:int, end:int ) : int
  requires 0 <= start && start <= end && end <= a.Length
  reads a
  {
    if (start == end) then 0 else sumTo(a, start, end-1) + a[end-1]
  }

//IMPL 
/* code modified by LLM (iteration 1): removed redundant null check since array<int> is non-null */
method SumInRange(a: array<int>, start: int, end: int) returns (sum: int)
  requires 0 <= start && start <= end && end <= a.Length
  ensures sum == sumTo(a, start, end)
{
  sum := 0;
  var i := start;
  while i < end
    invariant start <= i <= end
    invariant sum == sumTo(a, start, i)
  {
    sum := sum + a[i];
    i := i + 1;
  }
}