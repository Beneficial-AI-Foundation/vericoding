//ATOM
function sumTo( a:array<int>, start:int, end:int ) : int
  requires a != null
  requires 0 <= start && start <= end && end <= a.Length
  reads a
  {
    if (start == end) then 0 else sumTo(a, start, end-1) + a[end-1]
  }

/* code modified by LLM (iteration 2): Added helper lemma to prove sumTo extension property */
lemma SumToExtension(a: array<int>, start: int, end: int)
  requires a != null
  requires 0 <= start < end <= a.Length
  ensures sumTo(a, start, end) == sumTo(a, start, end-1) + a[end-1]
{
  // This follows directly from the definition of sumTo
}

/* code modified by LLM (iteration 2): Added helper lemma to prove sumTo prefix property */
lemma SumToPrefix(a: array<int>, start: int, mid: int, end: int)
  requires a != null
  requires 0 <= start <= mid < end <= a.Length
  ensures sumTo(a, start, end) == sumTo(a, start, mid) + sumTo(a, mid, end)
  decreases end - mid
{
  if mid == end - 1 {
    SumToExtension(a, start, end);
  } else {
    SumToExtension(a, start, end);
    SumToPrefix(a, start, mid, end-1);
  }
}

//IMPL SumInRange
method SumInRange(a: array<int>, start: int, end: int) returns (sum: int)
  requires a != null
  requires 0 <= start && start <= end && end <= a.Length
  ensures sum == sumTo(a, start, end)
{
  sum := 0;
  var i := start;
  while i < end
    invariant start <= i <= end
    invariant sum == sumTo(a, start, i)
  {
    /* code modified by LLM (iteration 2): Use helper lemma to prove loop invariant maintenance */
    if i < end {
      SumToPrefix(a, start, i, i+1);
    }
    sum := sum + a[i];
    i := i + 1;
  }
}