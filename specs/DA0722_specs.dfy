// <vc-preamble>
const MOD: int := 1000000007

predicate ValidInput(A: int, B: int, n: int, x: int) {
  A >= 1 && B >= 1 && n >= 1 && x >= 1 &&
  A <= 1000000000 && B <= 1000000000 && x <= 1000000000 &&
  n <= 1000000000000000000
}

function ModPow(base: int, exp: int, mod: int): int
  requires mod > 0
  requires exp >= 0
  decreases exp
{
  if exp == 0 then 1 % mod
  else if exp % 2 == 0 then
    var half := ModPow(base, exp / 2, mod);
    (half * half) % mod
  else
    (base * ModPow(base, exp - 1, mod)) % mod
}

predicate ValidResult(result: int) {
  result >= 0 && result < MOD
}

function ExpectedResultA1(A: int, B: int, n: int, x: int): int
  requires A == 1
  requires n >= 0
{
  ((ModPow(A, n, MOD) * x) % MOD + (n * B) % MOD) % MOD
}

function ExpectedResultANot1(A: int, B: int, n: int, x: int): int
  requires A != 1
  requires n >= 0
{
  ((ModPow(A, n, MOD) * x) % MOD + 
   (B * (ModPow(A, n, MOD) - 1 + MOD) % MOD * ModPow(A - 1, MOD - 2, MOD)) % MOD) % MOD
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method solve(A: int, B: int, n: int, x: int) returns (result: int)
  requires ValidInput(A, B, n, x)
  ensures ValidResult(result)
  ensures A == 1 ==> result == ExpectedResultA1(A, B, n, x)
  ensures A != 1 ==> result == ExpectedResultANot1(A, B, n, x)
// </vc-spec>
// <vc-code>
{
  var fir := (ModPow(A, n, MOD) * x) % MOD;
  var sec: int;

  if A == 1 {
    sec := (n * B) % MOD;
  } else {
    var a_pow_n := ModPow(A, n, MOD);
    var numerator := (B * (a_pow_n - 1 + MOD)) % MOD;
    var inv_a_minus_1 := ModPow(A - 1, MOD - 2, MOD);
    sec := (numerator * inv_a_minus_1) % MOD;
  }

  result := (fir + sec) % MOD;
}
// </vc-code>
