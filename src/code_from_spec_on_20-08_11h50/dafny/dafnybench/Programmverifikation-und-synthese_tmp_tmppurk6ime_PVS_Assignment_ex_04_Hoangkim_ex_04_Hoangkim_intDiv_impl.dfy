method intDiv(n:int, d:int) returns (q:int, r:int)
requires n >= d && n >= 0 && d > 0 ;
ensures (d*q)+r == n && 0 <= q <= n/2 && 0 <= r < d; 

//b)c)

method intDivImpl(n:int, d:int) returns (q:int, r:int)
requires n >= d && n >= 0 && d > 0;
ensures (d*q)+r == n && 0 <= q <= n/2 && 0 <= r < d;
// </vc-spec>
// <vc-code>
{
  q := 0;
  r := n;
  
  while r >= d && q < n/2
    invariant (d*q)+r == n
    invariant 0 <= q <= n/2
    invariant r >= 0
    decreases r
  {
    q := q + 1;
    r := r - d;
  }
  
  // If r >= d, then q must be n/2 (since the loop exited)
  // We need to ensure r < d while keeping q <= n/2
  if r >= d {
    // Set q to the maximum allowed value n/2
    q := n / 2;
    r := n - d * q;
  }
}
// </vc-code>