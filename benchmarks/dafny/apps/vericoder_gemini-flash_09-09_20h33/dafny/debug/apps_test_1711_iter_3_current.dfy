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
function Modulo(a: int, b: int): int
  requires b > 0
  ensures 0 <= Modulo(a, b) < b
{
  (a % b + b) % b
}

function Power(base: int, exp: int, mod: int): int
  requires mod > 0
  requires exp >= 0
  ensures 0 <= Power(base, exp, mod) < mod
{
  if exp == 0 then 1
  else if exp % 2 == 0 then Power(Modulo(base * base, mod), exp / 2, mod)
  else Modulo(base * Power(Modulo(base * base, mod), exp / 2, mod), mod)
}

function Factorial(k: int, mod: int): int
  requires k >= 0
  requires mod > 0
  ensures 0 <= Factorial(k, mod) < mod
{
  if k == 0 then 1
  else Modulo(k * Factorial(k - 1, mod), mod)
}

function Inverse(n: int, mod: int): int
  requires mod > 0 && n > 0
  requires mod == 998244353 && 0 < n < mod // n and mod are coprime, mod is prime
  ensures 0 <= Inverse(n, mod) < mod
  ensures Modulo(n * Inverse(n, mod), mod) == 1
{
  Power(n, mod - 2, mod) // Fermat's Little Theorem (mod must be prime)
}

function Combination(n: int, k: int, mod: int): int
  requires n >= 0 && k >= 0 && n >= k
  requires mod > 0
  requires mod == 998244353 // mod must be prime for Inverse using Fermat's Little Theorem
  ensures 0 <= Combination(n, k, mod) < mod
{
  if k == 0 || k == n then 1
  else if k > n then 0
  else
    var num := Factorial(n, mod);
    var den := Modulo(Factorial(k, mod) * Factorial(n - k, mod), mod);
    Modulo(num * Inverse(den, mod), mod)
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
  var MOD := 998244353;
  if n == 2 {
    result := 0;
  } else {
    var comb_val := Combination(m, n - 1, MOD);
    var term1 := Modulo(comb_val * (n - 2), MOD);
    var power_val := Power(2, n - 3, MOD);
    result := Modulo(term1 * power_val, MOD);
  }
}
// </vc-code>

