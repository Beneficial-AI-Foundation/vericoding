method mroot3(n:int) returns (r:int) 
requires n>=0
ensures r>=0 && r*r <= n <(r+1)*(r+1)
// </vc-spec>
// <vc-code>
{
  if n == 0 {
    r := 0;
    return;
  }
  
  var low := 0;
  var high := n;
  
  // Binary search for the square root
  while low <= high 
    invariant 0 <= low <= high + 1
    invariant low == 0 || (low - 1) * (low - 1) <= n
    invariant (high + 1) * (high + 1) > n
    decreases high - low
  {
    var mid := (low + high) / 2;
    var midSquared := mid * mid;
    
    if midSquared == n {
      r := mid;
      return;
    } else if midSquared < n {
      low := mid + 1;
    } else {
      high := mid - 1;
    }
  }
  
  r := high;
}
// </vc-code>