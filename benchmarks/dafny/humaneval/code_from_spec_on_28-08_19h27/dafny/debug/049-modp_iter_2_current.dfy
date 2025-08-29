function modp_rec(n: int, p: int): int
  requires p > 0
  requires n >= 0
{
    if n == 0 then 1 % p else (modp_rec(n - 1, p) * 2) % p
}

// <vc-helpers>
lemma mod_mul_distributive(a: int, b: int, p: int)
  requires p > 0
  ensures (a % p * b) % p == (a * b) % p
{
}

lemma modp_rec_correct(n: int, p: int)
  requires p > 0
  requires n >= 0
  ensures modp_rec(n, p) == pow(2, n) % p
  decreases n
{
  if n == 0 {
    assert modp_rec(0, p) == 1 % p == pow(2, 0) % p;
  } else {
    modp_rec_correct(n - 1, p);
    mod_mul_distributive(pow(2, n - 1), 2, p);
    assert pow(2, n) == pow(2, n - 1) * 2;
    assert modp_rec(n, p) == (modp_rec(n - 1, p) * 2) % p;
    assert modp_rec(n - 1, p) == pow(2, n - 1) % p;
    assert modp_rec(n, p) == (pow(2, n - 1) % p * 2) % p;
    assert modp_rec(n, p) == (pow(2, n - 1) * 2) % p;
    assert modp_rec(n, p) == pow(2, n) % p;
  }
}

function pow(base: int, exp: int): int
  requires exp >= 0
{
  if exp == 0 then 1 else base * pow(base, exp - 1)
}
// </vc-helpers>

// <vc-description>
/*
function_signature: def modp(n: Nat, p: Nat) -> Nat
Return 2^n modulo p (be aware of numerics).
*/
// </vc-description>

// <vc-spec>
function modp(n: int, p: int): int
  requires p > 0
  requires n >= 0
  ensures modp(n, p) == pow(2, n) % p
  ensures 0 <= modp(n, p) < p
// </vc-spec>
// <vc-code>
{
  modp_rec_correct(n, p);
  modp_rec(n, p)
}
// </vc-code>
