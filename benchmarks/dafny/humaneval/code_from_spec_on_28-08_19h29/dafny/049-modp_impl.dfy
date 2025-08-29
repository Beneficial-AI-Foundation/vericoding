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

lemma ModPProperties(n: int, p: int)
  requires p > 0
  requires n >= 0
  ensures modp_rec(n, p) == Power(2, n) % p
{
  if n == 0 {
    assert modp_rec(0, p) == 1 % p;
    assert Power(2, 0) == 1;
  } else {
    ModPProperties(n - 1, p);
    assert modp_rec(n, p) == (modp_rec(n - 1, p) * 2) % p;
    assert modp_rec(n - 1, p) == Power(2, n - 1) % p;
    assert Power(2, n - 1) * 2 == Power(2, n);
  }
}

function Power(base: int, exp: int): int
  requires exp >= 0
{
  if exp == 0 then 1 else base * Power(base, exp - 1)
}
// </vc-helpers>

// <vc-description>
/*
function_signature: def modp(n: Nat, p: Nat) -> Nat
Return 2^n modulo p (be aware of numerics).
*/
// </vc-description>

// <vc-spec>
method modp(n: int, p: int) returns (res: int)
  requires p > 0
  requires n >= 0
  ensures res == Power(2, n) % p
// </vc-spec>
// <vc-code>
{
  res := modp_rec(n, p);
}
// </vc-code>
