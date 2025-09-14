//Problem 01

//problem02
//a)

// <vc-helpers>
// No changes needed
// </vc-helpers>

// <vc-spec>
method intDiv(n:int, d:int) returns (q:int, r:int)
requires n >= d && n >= 0 && d > 0 ;
ensures (d*q)+r == n && 0 <= q <= n/2 && 0 <= r < d;
// </vc-spec>
// <vc-code>
{
  var q := 0;
  var r := n;
  while r >= d
    invariant d * q + r == n
    invariant r >= 0
  {
    r := r - d;
    q := q + 1;
  }
}
// </vc-code>

