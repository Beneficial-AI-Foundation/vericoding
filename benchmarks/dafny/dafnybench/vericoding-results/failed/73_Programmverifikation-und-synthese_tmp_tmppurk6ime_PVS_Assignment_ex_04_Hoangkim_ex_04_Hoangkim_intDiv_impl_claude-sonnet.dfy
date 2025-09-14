//Problem 01

//problem02
//a)

// <vc-helpers>
lemma DivisionProperties(n: int, d: int)
  requires n >= 0 && d > 0
  ensures n / d >= 0
  ensures n / d <= n
  ensures (n / d) * d <= n < (n / d + 1) * d
{
}

lemma QuotientBound(n: int, d: int)
  requires n >= d && d > 0
  ensures n / d >= 1
{
}
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
  
  while r >= d && q < n / 2
    invariant d * q + r == n
    invariant r >= 0
    invariant q >= 0
    invariant q <= n / 2
    decreases r
  {
    q := q + 1;
    r := r - d;
  }
}
// </vc-code>

