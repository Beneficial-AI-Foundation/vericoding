predicate ValidInput(n: int, a: int, b: int, p: int, q: int) {
  n > 0 && a > 0 && b > 0 && p > 0 && q > 0
}

function gcd(a: int, b: int): int
  requires a > 0 && b >= 0
  ensures gcd(a, b) > 0
  decreases b
{
  if b == 0 then a else gcd(b, a % b)
}

// <vc-helpers>
function MultiplyMod(x: int, y: int, m: int): int
    requires m > 0
    ensures 0 <= MultiplyMod(x, y, m) < m
{
    (x % m * y % m) % m
}

function PowerMod(base: int, exp: int, mod: int): int
    requires mod > 0 && exp >= 0
    ensures 0 <= PowerMod(base, exp, mod) < mod
    decreases exp
{
    if exp == 0 then 1 % mod
    else if exp % 2 == 0 then PowerMod(MultiplyMod(base, base, mod), exp / 2, mod)
    else MultiplyMod(base, PowerMod(MultiplyMod(base, base, mod), exp / 2, mod), mod)
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, a: int, b: int, p: int, q: int) returns (result: int)
  requires ValidInput(n, a, b, p, q)
  ensures result >= 0
// </vc-spec>
// <vc-code>
{
  var M := p * q;
  var phi_M := (p - 1) * (q - 1);
  var exp_val := n % phi_M;

  if exp_val == 0 && n != 0 {
    exp_val := phi_M;
  }
  
  // Calculate a^n mod M
  var an_mod_M := PowerMod(a, exp_val, M);

  // Calculate b^n mod M
  var bn_mod_M := PowerMod(b, exp_val, M);

  // Calculate (a^n + b^n) mod M
  result := (an_mod_M + bn_mod_M) % M;
}
// </vc-code>

