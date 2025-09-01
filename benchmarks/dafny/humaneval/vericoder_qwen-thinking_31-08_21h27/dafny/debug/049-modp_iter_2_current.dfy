function modp_rec(n: int, p: int): int
  requires p > 0
  requires n >= 0
{
    if n == 0 then 1 % p else (modp_rec(n - 1, p) * 2) % p
}

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method modp(n: int, p: int) returns (r: int)
  // pre-conditions-start
  requires p > 0
  requires n >= 0
  // pre-conditions-end
  // post-conditions-start
  ensures r == modp_rec(n, p)
  // post-conditions-end
// </vc-spec>
// <vc-code>
var result := 1 % p;
for i in 0..n {
    invariant result == modp_rec(i, p)
    result := (result * 2) % p;
}
return result;
// </vc-code>

