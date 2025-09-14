//Problem 01

//problem02
//a)

// <vc-helpers>
// No helpers needed for this implementation
// </vc-helpers>

// <vc-spec>
method intDiv(n:int, d:int) returns (q:int, r:int)
requires n >= d && n >= 0 && d > 0 ;
ensures (d*q)+r == n && 0 <= q <= n/2 && 0 <= r < d;
// </vc-spec>
// <vc-code>
{
  q := 0;
  r := n;
  while r >= d
    invariant 0 <= q <= n
    invariant 0 <= r <= n
    invariant d * q + r == n
  {
    r := r - d;
    q := q + 1;
  }
}
// </vc-code>

