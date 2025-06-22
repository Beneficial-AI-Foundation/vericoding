//IMPL 
method SquareRoot(N:nat) returns (r:nat)
  ensures r*r <= N < (r+1)*(r+1)
{
  if N == 0 {
    return 0;
  }
  
  var low := 0;
  var high := N;
  
  /* code modified by LLM (iteration 4): Fixed binary search with correct invariants and bounds */
  while low + 1 < high
    invariant 0 <= low < high <= N
    invariant low * low <= N
    invariant N < high * high
    decreases high - low
  {
    /* code modified by LLM (iteration 4): Use proper binary search midpoint calculation */
    var mid := low + (high - low) / 2;
    
    if mid * mid <= N {
      /* code modified by LLM (iteration 4): mid satisfies lower bound, update low */
      low := mid;
    } else {
      /* code modified by LLM (iteration 4): mid violates upper bound, update high */
      high := mid;
    }
  }
  
  /* code modified by LLM (iteration 4): Loop terminates when low + 1 >= high */
  assert low + 1 >= high;
  assert low * low <= N;
  assert N < high * high;
  
  /* code modified by LLM (iteration 4): Since low < high from invariant and low + 1 >= high, we must have low + 1 == high */
  assert low + 1 == high;
  assert N < (low + 1) * (low + 1);
  return low;
}