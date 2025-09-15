// <vc-preamble>
function modp_rec(n: int, p: int): int
  requires p > 0
  requires n >= 0
{
    if n == 0 then 1 % p else (modp_rec(n - 1, p) * 2) % p
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method modp(n: int, p: int) returns (r: int)

  requires p > 0
  requires n >= 0

  ensures r == modp_rec(n, p)
// </vc-spec>
// <vc-code>
{
  r := 1 % p;
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant r == modp_rec(i, p)
    invariant p > 0
  {
    r := (r * 2) % p;
    i := i + 1;
  }
}
// </vc-code>
