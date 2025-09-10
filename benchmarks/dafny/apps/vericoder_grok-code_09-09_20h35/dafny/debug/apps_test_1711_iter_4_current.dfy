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

function Power(a: nat, b: nat, mod: nat): nat
  requires mod > 1
  decreases b
{
  if b == 0 then 1
  else
    var a_sq = (a * a) % mod;
    var p = Power(a_sq, b / 2, mod);
    if b % 2 == 0 then p else (p * a) % mod
}

function ModInverse(a: nat, mod: nat): nat
  requires mod > 1 && a > 0
  decreases mod
{
  Power(a, mod - 2, mod)
}

function Combination(m: nat, k: nat, mod: nat): nat
  requires mod > 1 && 0 <= k <= m
  decreases k
{
  if k == 0 then 1
  else ((m % mod) * Combination(m - 1, k - 1, mod) * ModInverse(k, mod)) % mod
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
  result := if n == 2 then 0 else (((Combination(m, n - 1, 998244353) * (n - 2)) % 998244353) * Power(2, n - 3, 998244353)) % 998244353;
}
// </vc-code>

