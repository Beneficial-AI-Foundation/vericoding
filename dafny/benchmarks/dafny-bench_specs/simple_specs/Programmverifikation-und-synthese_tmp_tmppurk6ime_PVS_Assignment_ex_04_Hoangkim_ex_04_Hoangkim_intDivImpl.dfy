// SPEC

//b)c)

method intDivImpl(n:int, d:int) returns (q:int, r:int)
requires n >= d && n >= 0 && d > 0
ensures (d*q)+r == n && 0 <= q <= n/2 && 0 <= r < d; 
{
}
