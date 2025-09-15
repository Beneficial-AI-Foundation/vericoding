// <vc-preamble>
function modp_rec(n: int, p: int): int
  requires p > 0
  requires n >= 0
{
    if n == 0 then 1 % p else (modp_rec(n - 1, p) * 2) % p
}
// </vc-preamble>

// <vc-helpers>
lemma ModpRecUnfold(i: int, p: int)
  requires p > 0
  requires i >= 0
  ensures modp_rec(i + 1, p) == (modp_rec(i, p) * 2) % p
{ }
// </vc-helpers>

// <vc-spec>
method modp(n: int, p: int) returns (r: int)

  requires p > 0
  requires n >= 0

  ensures r == modp_rec(n, p)
// </vc-spec>
// <vc-code>
{
  var i := 0;
  var res := 1 % p;
  while i < n
    invariant 0 <= i
    invariant i <= n
    invariant res == modp_rec(i, p)
    decreases n - i
  {
    assert modp_rec(i + 1, p) == (modp_rec(i, p) * 2) % p;
    res := (res * 2) % p;
    i := i + 1;
  }
  r := res;
}
// </vc-code>
