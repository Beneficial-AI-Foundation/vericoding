predicate ValidInput(n: int, m: int) {
  1 <= n <= 100 && 1 <= m <= n && m <= 5
}

function power(base: int, exp: int): int
  requires exp >= 0
  decreases exp
{
  if exp == 0 then 1 else base * power(base, exp - 1)
}

function ExpectedTime(n: int, m: int): int
  requires ValidInput(n, m)
{
  (1900 * m + 100 * (n - m)) * power(2, m)
}

// <vc-helpers>
lemma PowerDivisionLemma(exp: int)
  requires exp > 0
  ensures power(2, exp) == 2 * power(2, exp - 1)
{
}

lemma InvariantUpdateLemma(n: int, m: int, i: int)
  requires ValidInput(n, m) && 0 <= i < m
  ensures 1900 * (m - i - 1) * power(2, m - i - 1) + 100 * (n - m) * (power(2, m - i - 1) - 1) + 1900 * power(2, m - i - 1)
          == 1900 * (m - i) * power(2, m - i) + 100 * (n - m) * (power(2, m - i) - 1)
{
  var p_prev := power(2, m - i - 1);
  var p_current := power(2, m - i);
  assert p_current == 2 * p_prev;
  
  calc {
    1900 * (m - i - 1) * p_prev + 100 * (n - m) * (p_prev - 1) + 1900 * p_prev;
    ==
    1900 * p_prev * (m - i - 1 + 1) + 100 * (n - m) * (p_prev - 1);
    ==
    1900 * (m - i) * p_prev + 100 * (n - m) * (p_prev - 1);
    ==
    1900 * (m - i) * (p_current / 2) + 100 * (n - m) * (p_current / 2 - 1);
    ==
    (1900 * (m - i) * p_current) / 2 + (100 * (n - m) * (p_current - 2)) / 2;
    ==
    [1900 * (m - i) * p_current + 100 * (n - m) * (p_current - 2)] / 2;
    ==
    [1900 * (m - i) * p_current + 100 * (n - m) * p_current - 200 * (n - m)] / 2;
    ==
    [(1900 * (m - i) + 100 * (n - m)) * p_current - 200 * (n - m)] / 2;
  }
  
  calc {
    1900 * (m - i) * p_current + 100 * (n - m) * (p_current - 1);
    ==
    1900 * (m - i) * p_current + 100 * (n - m) * p_current - 100 * (n - m);
    ==
    (1900 * (m - i) + 100 * (n - m)) * p_current - 100 * (n - m);
  }
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, m: int) returns (result: int)
  requires ValidInput(n, m)
  ensures result == ExpectedTime(n, m)
// </vc-spec>
// <vc-code>
{
  var total: int := 0;
  var attempts: int := 1;
  var i: int := m;
  
  while i > 0
    invariant 0 <= i <= m
    invariant attempts == power(2, m - i)
    invariant total == 1900 * (m - i) * power(2, m - i) + 100 * (n - m) * (power(2, m - i) - 1)
    decreases i
  {
    total := total + 1900 * attempts;
    attempts := attempts * 2;
    i := i - 1;
    
    // Prove the invariant holds after the update
    InvariantUpdateLemma(n, m, i);
  }
  
  // Add the time for the remaining n-m tests that pass on first attempt
  result := total + 100 * (n - m);
}
// </vc-code>

