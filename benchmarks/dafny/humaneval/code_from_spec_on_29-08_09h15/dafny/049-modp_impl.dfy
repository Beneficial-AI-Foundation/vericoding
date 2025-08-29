function modp_rec(n: int, p: int): int
  requires p > 0
  requires n >= 0
{
    if n == 0 then 1 % p else (modp_rec(n - 1, p) * 2) % p
}

// <vc-helpers>
lemma modp_rec_equiv(n: int, p: int, base: int, exp: int)
  requires p > 0
  requires n >= 0
  requires exp >= 0
  requires base >= 0
  requires exp == n
  requires base == 2
  ensures modp_rec(n, p) == pow_mod(base, exp, p, 1)
{
  if n == 0 {
    assert modp_rec(0, p) == 1 % p;
    assert pow_mod(base, 0, p, 1) == 1 % p;
  } else {
    modp_rec_equiv(n - 1, p, base, exp - 1);
    assert modp_rec(n - 1, p) == pow_mod(base, exp - 1, p, 1);
    assert modp_rec(n, p) == (modp_rec(n - 1, p) * 2) % p;
    assert pow_mod(base, exp, p, 1) == pow_mod(base, exp - 1, p, (1 * base) % p);
    assert (1 * base) % p == 2 % p;
    assert pow_mod(base, exp, p, 1) == pow_mod(base, exp - 1, p, 2 % p);
    pow_mod_property(base, exp - 1, p, 2 % p);
    assert pow_mod(base, exp - 1, p, 2 % p) == (pow_mod(base, exp - 1, p, 1) * 2) % p;
  }
}

function pow_mod(base: int, exp: int, p: int, acc: int): int
  requires p > 0
  requires exp >= 0
  requires acc >= 0
  decreases exp
{
  if exp == 0 then acc % p
  else pow_mod(base, exp - 1, p, (acc * base) % p)
}

lemma pow_mod_property(base: int, exp: int, p: int, acc: int)
  requires p > 0
  requires exp >= 0
  requires base >= 0
  requires acc >= 0
  ensures pow_mod(base, exp, p, acc) == (pow_mod(base, exp, p, 1) * acc) % p
  decreases exp
{
  if exp == 0 {
    assert pow_mod(base, 0, p, acc) == acc % p;
    assert pow_mod(base, 0, p, 1) == 1 % p;
    assert (pow_mod(base, 0, p, 1) * acc) % p == (1 * acc) % p == acc % p;
  } else {
    pow_mod_property(base, exp - 1, p, (acc * base) % p);
    pow_mod_property(base, exp - 1, p, (1 * base) % p);
    assert pow_mod(base, exp - 1, p, (acc * base) % p) == (pow_mod(base, exp - 1, p, 1) * ((acc * base) % p)) % p;
    assert pow_mod(base, exp - 1, p, (1 * base) % p) == (pow_mod(base, exp - 1, p, 1) * ((1 * base) % p)) % p;
  }
}

lemma pow_mod_correctness(base: int, exp: int, p: int)
  requires p > 0
  requires exp >= 0
  requires base >= 0
  requires base == 2
  ensures pow_mod(base, exp, p, 1) == modp_rec(exp, p)
{
  if exp == 0 {
    assert pow_mod(base, 0, p, 1) == 1 % p;
    assert modp_rec(0, p) == 1 % p;
  } else {
    pow_mod_correctness(base, exp - 1, p);
    assert pow_mod(base, exp - 1, p, 1) == modp_rec(exp - 1, p);
    assert pow_mod(base, exp, p, 1) == pow_mod(base, exp - 1, p, (1 * base) % p);
    assert (1 * base) % p == 2 % p;
    assert pow_mod(base, exp, p, 1) == pow_mod(base, exp - 1, p, 2 % p);
    pow_mod_property(base, exp - 1, p, 2 % p);
    assert pow_mod(base, exp - 1, p, 2 % p) == (pow_mod(base, exp - 1, p, 1) * 2) % p;
    assert modp_rec(exp, p) == (modp_rec(exp - 1, p) * 2) % p;
  }
}

lemma modp_rec_step(i: int, p: int)
  requires p > 0
  requires i >= 0
  ensures modp_rec(i + 1, p) == (modp_rec(i, p) * 2) % p
{
}

lemma modp_rec_base_case(p: int)
  requires p > 0
  ensures modp_rec(0, p) == 1 % p
{
}
// </vc-helpers>

// <vc-description>
/*
function_signature: def modp(n: Nat, p: Nat) -> Nat
Return 2^n modulo p (be aware of numerics).
*/
// </vc-description>

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
  modp_rec_base_case(p);
  r := 1 % p;
  var i := 0;
  
  while i < n
    invariant 0 <= i <= n
    invariant r == modp_rec(i, p)
  {
    modp_rec_step(i, p);
    r := (r * 2) % p;
    i := i + 1;
  }
}
// </vc-code>

