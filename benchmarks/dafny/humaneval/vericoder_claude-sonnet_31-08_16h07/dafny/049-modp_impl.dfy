function modp_rec(n: int, p: int): int
  requires p > 0
  requires n >= 0
{
    if n == 0 then 1 % p else (modp_rec(n - 1, p) * 2) % p
}

// <vc-helpers>
lemma modp_rec_property(n: int, p: int)
  requires p > 0
  requires n >= 0
  ensures modp_rec(n, p) == if n == 0 then 1 % p else (modp_rec(n - 1, p) * 2) % p
{
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
  if n == 0 {
    r := 1 % p;
  } else {
    var prev := modp(n - 1, p);
    r := (prev * 2) % p;
  }
}
// </vc-code>

