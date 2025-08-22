//IMPL 
method SquareRoot(N:nat) returns (r:nat)
  ensures r*r <= N < (r+1)*(r+1)
{
  if N == 0 {
    return 0;
  }
  
  var low := 0;
  var high := N;
  
  /* code modified by LLM (iteration 1): Fixed loop invariants to maintain proper bounds and adjusted search logic */
  while low < high
    invariant 0 <= low <= high <= N
    invariant low * low <= N
    invariant N < (high + 1) * (high + 1)
  {
    var mid := low + (high - low) / 2;
    
    /* code modified by LLM (iteration 1): Fixed the condition to properly narrow the search space */
    if (mid + 1) * (mid + 1) <= N {
      low := mid + 1;
    } else {
      high := mid;
    }
  }
  
  /* code modified by LLM (iteration 1): Return low directly as it now represents the correct square root */
  r := low;
}