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
function Power(base: int, exp: int, mod: int): int
  requires mod > 0
  requires exp >= 0
{
  if exp == 0 then 1 % mod
  else (base * Power(base, exp - 1, mod)) % mod
}

function Factorial(n: int, mod: int): int
  requires n >= 0
  requires mod > 0
{
  if n == 0 then 1
  else (n * Factorial(n - 1, mod)) % mod
}

function ModInverse(a: int, mod: int): int
  requires mod > 0
  requires a > 0
{
  Power(a, mod - 2, mod)
}

function Combination(m: int, k: int, mod: int): int
  requires m >= 0
  requires k >= 0
  requires k <= m
  requires mod > 0
{
  if k == 0 || k == m then 1
  else if k > m then 0
  else
    var numerator := Factorial(m, mod);
    var denominator := (Factorial(k, mod) * Factorial(m - k, mod)) % mod;
    (numerator * ModInverse(denominator, mod)) % mod
}

lemma PowerNonnegative(base: int, exp: int, mod: int)
  requires mod > 0
  requires exp >= 0
  ensures Power(base, exp, mod) >= 0
{
}

lemma PowerBounded(base: int, exp: int, mod: int)
  requires mod > 0
  requires exp >= 0
  ensures Power(base, exp, mod) < mod
{
}

lemma CombinationNonnegative(m: int, k: int, mod: int)
  requires m >= 0
  requires k >= 0
  requires k <= m
  requires mod > 0
  ensures Combination(m, k, mod) >= 0
{
}

lemma CombinationBounded(m: int, k: int, mod: int)
  requires m >= 0
  requires k >= 0
  requires k <= m
  requires mod > 0
  ensures Combination(m, k, mod) < mod
{
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
  } else {
    var comb := Combination(m, n - 1, 998244353);
    var temp1 := (comb * (n - 2)) % 998244353;
    var power := Power(2, n - 3, 998244353);
    result := (temp1 * power) % 998244353;
    
    PowerNonnegative(2, n - 3, 998244353);
    PowerBounded(2, n - 3, 998244353);
    CombinationNonnegative(m, n - 1, 998244353);
    CombinationBounded(m, n - 1, 998244353);
  }
}
// </vc-code>

