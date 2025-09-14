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
function Power(base: int, exponent: int, modulus: int): int
  requires exponent >= 0 && modulus > 1
  decreases exponent
{
  if exponent == 0 then 1
  else (base * Power(base, exponent - 1, modulus)) % modulus
}

function Combination(n: int, k: int, modulus: int): int
  requires 0 <= k <= n && modulus > 1
  decreases n
{
  if k == 0 || k == n then 1
  else (Combination(n - 1, k - 1, modulus) + Combination(n - 1, k, modulus)) % modulus
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
    return 0;
  } else {
    var comb := Combination(m, n - 1, 998244353);
    var term1 := (comb * (n - 2)) % 998244353;
    var pow2 := Power(2, n - 3, 998244353);
    return (term1 * pow2) % 998244353;
  }
}
// </vc-code>

