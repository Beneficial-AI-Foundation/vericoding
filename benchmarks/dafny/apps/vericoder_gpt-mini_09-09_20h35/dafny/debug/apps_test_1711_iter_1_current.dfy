predicate ValidInput(n: int, m: int) {
  n >= 2 && m >= 1 && n <= m && m <= 200000
}

function ExpectedResult(n: int, m: int): int
  requires ValidInput(n, m)
{
  if n == 2 then 0
  else (((Combination(m, n - 1, 998244353) * (n - 2)) % 998244353) * Power(2, n - 3, 998244353)) % 998244353
}

predicate ValidOutput(result: int) {
  0 <= result < 998244353
}

// <vc-helpers>
const MOD: int := 998244353

function Power(base: int, exp: int, mod: int): int
  requires mod > 0 && exp >= 0
  decreases exp
{
  if exp == 0 then 1 % mod
  else if exp % 2 == 0 then
    var half := Power(base, exp / 2, mod);
    (half * half) % mod
  else
    ((base % mod) * Power(base, exp - 1, mod)) % mod
}

function Inv(a: int, mod: int): int
  requires 0 < a < mod && mod > 1
{
  Power(a, mod - 2, mod)
}

function Combination(m: int, k: int, mod: int): int
  requires 0 <= k <= m && mod > 1
  decreases (k, m)
{
  if k == 0 then 1 % mod
  else
    var part := (m % mod) * Combination(m - 1, k - 1, mod) % mod;
    (part * Inv(k, mod)) % mod
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, m: int) returns (result: int)
  requires ValidInput(n, m)
  ensures ValidOutput(result)
  ensures result == ExpectedResult(n, m)
// </vc-spec>
// <vc-code>
{
  if n == 2 {
    result := 0;
    return;
  }
  var mod := 998244353;
  result := ((Combination(m, n - 1, mod) * (n - 2)) % mod * Power(2, n - 3, mod)) % mod;
  if result < 0 {
    result := result + mod;
  }
}
// </vc-code>

