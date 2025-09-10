predicate ValidInput(n: int, k: int)
{
  4 <= n <= 1000 && 1 <= k <= 4 && k < n
}

function factorial(n: int): int
  requires n >= 0
  ensures factorial(n) > 0
{
  if n <= 1 then 1 else n * factorial(n - 1)
}

function derangement(n: int): int
  requires n >= 0
  ensures derangement(n) >= 0
{
  if n <= 1 then 0
  else if n == 2 then 1
  else (n - 1) * (derangement(n - 1) + derangement(n - 2))
}

function binomial(n: int, k: int): int
  requires n >= 0 && k >= 0
  ensures binomial(n, k) >= 0
{
  if k > n then 0
  else if k == 0 || k == n then 1
  else factorial(n) / (factorial(k) * factorial(n - k))
}

function sum_binomial_derangement(n: int, k: int, i: int): int
  requires n >= 0 && k >= 0 && i >= 0
  ensures sum_binomial_derangement(n, k, i) >= 0
  decreases n - k - i
{
  if i >= n - k then 0
  else binomial(n, i) * derangement(n - i) + sum_binomial_derangement(n, k, i + 1)
}

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method solve(n: int, k: int) returns (result: int)
  requires ValidInput(n, k)
  ensures result == factorial(n) - sum_binomial_derangement(n, k, 0)
// </vc-spec>
// <vc-code>
{
  var fact_n := factorial(n);
  var sum := sum_binomial_derangement(n, k, 0);
  result := fact_n - sum;
}
// </vc-code>

