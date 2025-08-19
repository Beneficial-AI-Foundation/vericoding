function sumTo( a:array<int>, n:int ) : int
 requires 0 <= n && n <= a.Length
 reads a
{
 if (n == 0) then 0 else sumTo(a, n-1) + a[n-1]
}

//IMPL 
method ArraySum(a: array<int>) returns (result: int)
  ensures result == sumTo(a, a.Length)
{
  /* code modified by LLM (iteration 1): Added initialization and loop structure with proper invariants */
  result := 0;
  var i := 0;
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant result == sumTo(a, i)
  {
    /* code modified by LLM (iteration 1): Added array access and increment operations */
    result := result + a[i];
    i := i + 1;
  }
}