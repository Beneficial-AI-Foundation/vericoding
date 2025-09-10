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
function Combination(n: int, k: int, mod: int): int
  requires n >= 0 && k >= 0 && mod > 0
  ensures 0 <= Combination(n, k, mod) < mod
{
  if k < 0 || k > n then 0
  else if k == 0 || k == n then 1 % mod
  else (Combination(n - 1, k - 1, mod) + Combination(n - 1, k, mod)) % mod
}

function Power(base: int, exponent: int, mod: int): int
  requires base >= 0 && exponent >= 0 && mod > 0
  ensures 0 <= Power(base, exponent, mod) < mod
{
  if exponent == 0 then
    1 % mod
  else if exponent % 2 == 0 then
    (var half := Power(base, exponent / 2, mod);
    (half * half) % mod)
  else
    (base * Power(base, exponent - 1, mod)) % mod
}

lemma CombinationLemma(n: int, k: int, mod: int)
  requires n >= 0 && k >= 0 && mod > 0
  ensures Combination(n, k, mod) == if k < 0 || k > n then 0 else if k == 0 || k == n then 1 % mod else (Combination(n - 1, k - 1, mod) + Combination(n - 1, k, mod)) % mod
{
}

lemma PowerLemma(base: int, exponent: int, mod: int)
  requires base >= 0 && exponent >= 0 && mod > 0
  ensures Power(base, exponent, mod) == if exponent == 0 then 1 % mod else if exponent % 2 == 0 then (var half := Power(base, exponent / 2, mod); (half * half) % mod) else (base * Power(base, exponent - 1, mod)) % mod
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
    var term1 := (comb * (n - 2)) % 998244353;
    var pow := Power(2, n - 3, 998244353);
    result := (term1 * pow) % 998244353;
  }
}
// </vc-code>

