function modp_rec(n: int, p: int): int
  requires p > 0
  requires n >= 0
{
    if n == 0 then 1 % p else (modp_rec(n - 1, p) * 2) % p
}
// pure-end
method modp(n: int, p: int) returns (r: int)
  // pre-conditions-start
  requires p > 0
  requires n >= 0
  // pre-conditions-end
  // post-conditions-start
  ensures r == modp_rec(n, p)
  // post-conditions-end
{
  // impl-start
  r := 1 % p;
  var i := 0;
  while i < n
    // invariants-start
    invariant 0 <= i <= n
    invariant r == modp_rec(i, p)
    // invariants-end
  {
    r := (r * 2) % p;
    i := i + 1;
  }
  // impl-end
}
