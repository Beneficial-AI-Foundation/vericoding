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
  decreases if exp <= 0 then 0 else exp
{
  if mod <= 0 then 0
  else if exp <= 0 then 1 % mod
  else ((Power(base, exp - 1, mod) * (base % mod)) % mod)
}

function Combination(n: int, k: int, mod: int): int
  decreases if k <= 0 || k >= n || n <= 0 then 0 else n
{
  if mod <= 0 then 0
  else if k <= 0 || k >= n then 1 % mod
  else if n <= 0 then 0
  else (Combination(n - 1, k - 1, mod) + Combination(n - 1, k, mod)) % mod
}

lemma ExpectedResultValid(n: int, m: int)
  requires ValidInput(n, m)
  ensures ValidOutput(ExpectedResult(n, m))
{
  if n == 2 {
    assert ExpectedResult(n, m) == 0;
    assert 0 <= ExpectedResult(n, m) < 998244353;
  } else {
    var P := 998244353;
    var a := (((Combination(m, n - 1, P) * (n - 2)) % P) * Power(2, n - 3, P)) % P;
    assert ExpectedResult(n, m) == a;
    assert P > 0;
    assert 0 <= a < P;
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
  result := ExpectedResult(n, m);
  ExpectedResultValid(n, m);
  assert ValidOutput(result);
}
// </vc-code>

