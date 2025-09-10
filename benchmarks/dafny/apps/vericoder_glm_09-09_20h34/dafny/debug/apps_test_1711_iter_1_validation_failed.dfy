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
function {:axiom} Combination(n: int, k: int, MOD: int): int
  requires 0 <= k <= n
  requires MOD > 1
  ensures 0 <= Combination(n, k, MOD) < MOD

function Power(base: int, exp: int, MOD: int): int
  requires MOD > 1
  ensures 0 <= Power(base, exp, MOD) < MOD
  decreases exp
{
  if exp == 0 then 1
  else if exp % 2 == 0 then 
    var half := Power(base, exp / 2, MOD);
    (half * half) % MOD
  else
    (base * Power(base, exp - 1, MOD)) % MOD
}

function ModInverse(a: int, MOD: int): int
  requires 0 < a < MOD
  requires MOD > 1
  ensures (a * ModInverse(a, MOD)) % MOD == 1
  ensures 0 <= ModInverse(a, MOD) < MOD
{
  Power(a, MOD - 2, MOD)
}

function Factorial(n: int, MOD: int): int
  requires 0 <= n
  requires MOD > 1
  ensures 0 <= Factorial(n, MOD) < MOD
  decreases n
{
  if n == 0 then 1
  else (Factorial(n - 1, MOD) * n) % MOD
}

ghost lemma ExpectedResultFormula(n: int, m: int, MOD: int)
  requires ValidInput(n, m)
  requires MOD == 998244353
  ensures ExpectedResult(n, m) == 
    if n == 2 then 0
    else 
      var c := Combination(m, n - 1, MOD);
      var term1 := (c * (n - 2)) % MOD;
      var p := Power(2, n - 3, MOD);
      (term1 * p) % MOD
{
}

ghost lemma CombinationEqualsFactorialDefinition(n: int, k: int, MOD: int)
  requires 0 <= k <= n
  requires MOD > 1
  ensures Combination(n, k, MOD) == 
    var factN := Factorial(n, MOD);
    var factK := Factorial(k, MOD);
    var factNK := Factorial(n - k, MOD);
    var denom := (factK * factNK) % MOD;
    (factN * ModInverse(denom, MOD)) % MOD
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
  var MOD := 998244353;
  if n == 2 {
    return 0;
  }
  
  var c := Combination(m, n - 1, MOD);
  var term1 := (c * (n - 2)) % MOD;
  var p := Power(2, n - 3, MOD);
  result := (term1 * p) % MOD;
}
// </vc-code>

