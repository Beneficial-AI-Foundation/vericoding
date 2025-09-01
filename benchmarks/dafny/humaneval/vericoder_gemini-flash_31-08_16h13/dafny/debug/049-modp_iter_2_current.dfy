function modp_rec(n: int, p: int): int
  requires p > 0
  requires n >= 0
{
    if n == 0 then 1 % p else (modp_rec(n - 1, p) * 2) % p
}

// <vc-helpers>
function modp_rec(n: int, p: int): int
  requires p > 0
  requires n >= 0
{
    if n == 0 then 1 % p else (modp_rec(n - 1, p) * 2) % p
}
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
{
    var r_val := 1 % p; // Changed variable name to avoid "Duplicate local-variable name: r"
    var i := 0;
    while i < n
        invariant 0 <= i <= n
        invariant r_val == modp_rec(i, p) // Updated invariant to use the new variable name
    {
        r_val := (r_val * 2) % p;
        i := i + 1;
    }
    return r_val; // Returned the correct variable
}
// </vc-code>

