method SquareRoot(N:nat) returns (r:nat)
  ensures r*r <= N < (r+1)*(r+1)
// </vc-spec>
// <vc-code>
{
  if N == 0 {
    return 0;
  }
  
  var low := 0;
  var high := N + 1;  // Changed: ensure high*high > N initially;
  
  // Binary search invariant: low*low <= N and high*high > N
  while low + 1 < high
    invariant low * low <= N
    invariant high * high > N  // Simplified: always strictly greater
    invariant low < high
    decreases high - low
  {
    var mid := (low + high) / 2;
    var midSquared := mid * mid;
    
    if midSquared <= N {
      low := mid;
    } else {
      high := mid;
    }
  }
  
  // At this point, low + 1 >= high, so either low == high or low + 1 == high
  // We know low*low <= N and high*high > N
  
  if low == high {
    // This case is impossible because low*low <= N and high*high > N
    // but if low == high, we'd have low*low <= N < low*low, which is impossible
    r := low;
  } else {
    // low + 1 == high, and we know low*low <= N and (low+1)*(low+1) > N
    r := low;
  }
}
// </vc-code>