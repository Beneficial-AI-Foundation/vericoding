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
ghost method LemmaDerangementNonnegative(n: int)
  requires n >= 0
  ensures derangement(n) >= 0
{
  if n <= 1 {
    calc {
      derangement(n);
      { assert n <= 1; }
      0;
    }
  } else if n == 2 {
    calc {
      derangement(n);
      { assert n == 2; }
      1;
    }
  } else {
    calc {
      derangement(n);
      { assert n > 2; }
      (n - 1) * (derangement(n - 1) + derangement(n - 2));
    }
    LemmaDerangementNonnegative(n - 1);
    LemmaDerangementNonnegative(n - 2);
    calc {
      (n - 1) * (derangement(n - 1) + derangement(n - 2));
      >= { assert derangement(n - 1) >= 0 && derangement(n - 2) >= 0; }
      (n - 1) * (0 + 0);
      >= { assert n > 2; }
      0;
    }
  }
}

ghost method LemmaBinomialNonnegative(n: int, k: int)
  requires n >= 0 && k >= 0
  ensures binomial(n, k) >= 0
{
  if k > n {
    calc {
      binomial(n, k);
      { assert k > n; }
      0;
    }
  } else if k == 0 || k == n {
    calc {
      binomial(n, k);
      { assert k == 0 || k == n; }
      1;
    }
  } else {
    calc {
      binomial(n, k);
      { assert k > 0 && k < n; }
      factorial(n) / (factorial(k) * factorial(n - k));
    }
    assert factorial(n) > 0;
    assert factorial(k) > 0;
    assert factorial(n - k) > 0;
    assert factorial(k) * factorial(n - k) > 0;
    assert factorial(n) / (factorial(k) * factorial(n - k)) >= 0;
  }
}

ghost method LemmaSumBinomialDerangementDerivation(n: int, k: int, i: int)
  requires n >= 0 && k >= 0 && i >= 0 && i <= n - k
  ensures sum_binomial_derangement(n, k, i) == sum_binomial_derangement(n, k, i + 1) + binomial(n, i) * derangement(n - i)
  decreases n - k - i
{
  if i >= n - k {
    calc {
      sum_binomial_derangement(n, k, i);
      { assert i >= n - k; }
      0;
      == { assert i >= n - k; }
      0 + 0;
      == { assert i >= n - k; binomial(n, i) * derangement(n - i); }
      sum_binomial_derangement(n, k, i + 1) + 0;
      == { assert i >= n - k; LemmaBinomialNonnegative(n, i); LemmaDerangementNonnegative(n-i); }
      sum_binomial_derangement(n, k, i + 1) + binomial(n, i) * derangement(n - i);
    }
  } else {
    calc {
      sum_binomial_derangement(n, k, i);
      { assert i < n - k; }
      binomial(n, i) * derangement(n - i) + sum_binomial_derangement(n, k, i + 1);
      ==
      sum_binomial_derangement(n, k, i + 1) + binomial(n, i) * derangement(n - i);
    }
  }
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, k: int) returns (result: int)
  requires ValidInput(n, k)
  ensures result == factorial(n) - sum_binomial_derangement(n, k, 0)
// </vc-spec>
// <vc-code>
{
  assert ValidInput(n, k);
  LemmaDerangementNonnegative(n);
  LemmaBinomialNonnegative(n, 0);
  
  var sum := 0;
  var i := 0;

  while i < n - k
    invariant 0 <= i <= n - k
    invariant sum == sum_binomial_derangement(n, k, i)
    decreases n - k - i
  {
    LemmaSumBinomialDerangementDerivation(n, k, i);
    assert sum == sum_binomial_derangement(n, k, i);
    assert sum_binomial_derangement(n, k, i) == sum_binomial_derangement(n, k, i + 1) + binomial(n, i) * derangement(n - i);
    
    sum := sum + binomial(n, i) * derangement(n - i);
    i := i + 1;

    LemmaBinomialNonnegative(n, i);
    LemmaDerangementNonnegative(n - i);
  }

  LemmaSumBinomialDerangementDerivation(n, k, i);
  assert i == n - k;
  assert sum_binomial_derangement(n, k, n - k) == 0;
  assert sum == sum_binomial_derangement(n, k, 0);

  result := factorial(n) - sum;
}
// </vc-code>

