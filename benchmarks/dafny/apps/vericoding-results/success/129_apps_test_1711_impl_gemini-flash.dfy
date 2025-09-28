// <vc-preamble>
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
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): Ensure Combination returns value within modulus range */
function Combination(n: int, k: int, modulus: int): int
    requires 0 <= k <= n
    requires modulus > 0
    ensures 0 <= Combination(n, k, modulus) < modulus
  {
    if k == 0 || k == n then 1 % modulus // Ensure 1 is within modulus range
    else if k > n / 2 then Combination(n, n - k, modulus)
    else (
      (Combination(n - 1, k - 1, modulus) + Combination(n - 1, k, modulus)) % modulus
    )
  }

  /* helper modified by LLM (iteration 2): Ensure Power returns value within modulus range and termination */
  function Power(base: int, exp: int, modulus: int): int
    decreases exp
    requires exp >= 0
    requires modulus > 0
    ensures 0 <= Power(base, exp, modulus) < modulus
  {
    if exp == 0 then 1 % modulus // Ensure 1 is within modulus range
    else if exp % 2 == 0 then Power((base * base) % modulus, exp / 2, modulus)
    else (base * Power((base * base) % modulus, (exp - 1) / 2, modulus)) % modulus
  }
// </vc-helpers>

// <vc-spec>
method solve(n: int, m: int) returns (result: int)
  requires ValidInput(n, m)
  ensures ValidOutput(result)
  ensures result == ExpectedResult(n, m)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): Implemented the main logic for solve method */
{
    var MODULO := 998244353;
    if n == 2 {
      result := 0;
    } else {
      var term1 := Combination(m, n - 1, MODULO);
      var term2 := n - 2;
      var term3 := Power(2, n - 3, MODULO);
      result := ((((term1 * term2) % MODULO) * term3) % MODULO);
    }
  }
// </vc-code>
