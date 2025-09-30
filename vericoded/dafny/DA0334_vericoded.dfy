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
function Power(base: int, exp: nat, mod: int): int
  requires mod > 0
  ensures 0 <= Power(base, exp, mod) < mod
  decreases exp
{
  if exp == 0 then 1 % mod
  else if exp % 2 == 0 then
    var half := Power(base, exp / 2, mod);
    (half * half) % mod
  else
    ((base % mod) * Power(base, exp - 1, mod)) % mod
}

function Factorial(n: nat, mod: int): int
  requires mod > 0
  ensures 0 <= Factorial(n, mod) < mod
  decreases n
{
  if n == 0 then 1 % mod
  else ((n % mod) * Factorial(n - 1, mod)) % mod
}

function ModInverse(a: int, mod: int): int
  requires mod > 0
  requires 0 < a < mod
  ensures 0 <= ModInverse(a, mod) < mod
{
  Power(a, mod - 2, mod)
}

function Combination(n: int, k: int, mod: int): int
  requires mod > 0
  requires 0 <= k <= n
  ensures 0 <= Combination(n, k, mod) < mod
{
  if k == 0 || k == n then 1 % mod
  else if k > n then 0
  else 
    var num := Factorial(n, mod);
    var den1 := Factorial(k, mod);
    var den2 := Factorial(n - k, mod);
    var den := (den1 * den2) % mod;
    if den == 0 then 0
    else (num * ModInverse(den, mod)) % mod
}

method ComputePower(base: int, exp: nat, mod: int) returns (res: int)
  requires mod > 0
  ensures res == Power(base, exp, mod)
  ensures 0 <= res < mod
{
  if exp == 0 {
    res := 1 % mod;
  } else if exp % 2 == 0 {
    var half := ComputePower(base, exp / 2, mod);
    res := (half * half) % mod;
  } else {
    var prev := ComputePower(base, exp - 1, mod);
    res := ((base % mod) * prev) % mod;
  }
}

method ComputeFactorial(n: nat, mod: int) returns (res: int)
  requires mod > 0
  ensures res == Factorial(n, mod)
  ensures 0 <= res < mod
{
  res := 1 % mod;
  var i := 1;
  while i <= n
    invariant 1 <= i <= n + 1
    invariant 0 <= res < mod
    invariant res == Factorial(i - 1, mod)
  {
    res := (res * (i % mod)) % mod;
    i := i + 1;
  }
}

method ComputeModInverse(a: int, mod: int) returns (res: int)
  requires mod > 0
  requires 0 < a < mod
  ensures res == ModInverse(a, mod)
  ensures 0 <= res < mod
{
  res := ComputePower(a, mod - 2, mod);
}

method ComputeCombination(n: int, k: int, mod: int) returns (res: int)
  requires mod > 0
  requires 0 <= k <= n
  ensures res == Combination(n, k, mod)
  ensures 0 <= res < mod
{
  if k == 0 || k == n {
    res := 1 % mod;
  } else if k > n {
    res := 0;
  } else {
    var num := ComputeFactorial(n, mod);
    var den1 := ComputeFactorial(k, mod);
    var den2 := ComputeFactorial(n - k, mod);
    var den := (den1 * den2) % mod;
    if den == 0 {
      res := 0;
    } else {
      var inv := ComputeModInverse(den, mod);
      res := (num * inv) % mod;
    }
  }
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
  var mod := 998244353;
  
  if n == 2 {
    result := 0;
  } else {
    var comb := ComputeCombination(m, n - 1, mod);
    var pow := ComputePower(2, n - 3, mod);
    var temp1 := (comb * (n - 2)) % mod;
    result := (temp1 * pow) % mod;
  }
}
// </vc-code>

