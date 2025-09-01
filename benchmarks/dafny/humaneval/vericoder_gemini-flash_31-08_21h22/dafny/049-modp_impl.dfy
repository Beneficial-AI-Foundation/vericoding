function modp_rec(n: int, p: int): int
  requires p > 0
  requires n >= 0
{
    if n == 0 then 1 % p else (modp_rec(n - 1, p) * 2) % p
}

// <vc-helpers>
function modp_pow(n: int, p: int): int
  requires p > 0
  requires n >= 0
  ensures modp_pow(n, p) == modp_rec(n, p)
{
  if n == 0 then 1 % p
  else
    var r_prev := modp_pow(n - 1, p);
    (r_prev * 2) % p
}

lemma modp_pow_iterative(n: int, p: int)
  requires p > 0
  requires n >= 0
  ensures modp_pow(n, p) == modp_rec(n, p)
{
  // The recursive definition is already proven to be the same as modp_pow through the ensusre clause.
  // This lemma is just to make the verifier aware of this equivalence for the iterative solution.
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
  var r_val := 1 % p;
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant r_val == modp_rec(i, p)
  {
    r_val := (r_val * 2) % p;
    i := i + 1;
  }
  return r_val;
}
// </vc-code>

