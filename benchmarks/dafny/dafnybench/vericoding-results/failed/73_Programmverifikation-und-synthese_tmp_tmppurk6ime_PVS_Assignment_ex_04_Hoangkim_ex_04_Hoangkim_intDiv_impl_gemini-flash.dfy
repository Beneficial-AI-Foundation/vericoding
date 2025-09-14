//Problem 01

//problem02
//a)

// <vc-helpers>
function Modulo(n: int, d: int): int
  requires n >= 0 && d > 0
  ensures 0 <= Modulo(n, d) < d
{
  if n < d then n
  else Modulo(n - d, d)
}

function Divide(n: int, d: int): int
  requires n >= 0 && d > 0
  ensures n == Divide(n, d) * d + Modulo(n, d)
  ensures 0 <= Divide(n,d) <= n/d
{
  if n < d then 0
  else 1 + Divide(n - d, d)
}
// </vc-helpers>

// <vc-spec>
method intDiv(n:int, d:int) returns (q:int, r:int)
requires n >= d && n >= 0 && d > 0 ;
ensures (d*q)+r == n && 0 <= q <= n/2 && 0 <= r < d;
// </vc-spec>
// <vc-code>
{
  var q_val: int := 0;
  var r_val: int := n;

  while r_val >= d
    invariant r_val == n - q_val * d
    invariant r_val >= 0
    invariant q_val >= 0
    invariant q_val == (n - r_val) / d
  {
    q_val := q_val + 1;
    r_val := r_val - d;
  }
  q := q_val;
  r := r_val;
}
// </vc-code>

