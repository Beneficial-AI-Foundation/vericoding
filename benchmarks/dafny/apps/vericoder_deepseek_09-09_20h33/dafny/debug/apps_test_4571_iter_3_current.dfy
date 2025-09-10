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
lemma PowerLemma(base: int, exp: int)
  requires exp >= 0
  ensures power(2, exp) == (if exp == 0 then 1 else 2 * power(2, exp - 1))
{
  // This lemma is trivial and Dafny can prove it automatically
}

lemma PowerNonNegative(base: int, exp: int)
  requires exp >= 0 && base >= 0
  ensures power(base, exp) >= 0
{
  // Base case and inductive case for non-negative power
}

lemma ExpectedTimeLemma(n: int, m: int, k: int)
  requires ValidInput(n, m) && 0 <= k <= m
  ensures ExpectedTime(n, m) == (1900 * m + 100 * (n - m)) * power(2, m)
{
  // Trivial lemma - just establishes the definition
}

lemma PowerMultiplication(base: int, exp1: int, exp2: int)
  requires exp1 >= 0 && exp2 >= 0
  ensures power(base, exp1 + exp2) == power(base, exp1) * power(base, exp2)
  decreases exp1
{
  if exp1 == 0 {
    assert power(base, 0 + exp2) == 1 * power(base, exp2);
  } else {
    PowerMultiplication(base, exp1 - 1, exp2);
    assert power(base, exp1 + exp2) == base * power(base, exp1 - 1 + exp2);
    assert power(base, exp1 + exp2) == base * (power(base, exp1 - 1) * power(base, exp2));
    assert power(base, exp1 + exp2) == (base * power(base, exp1 - 1)) * power(base, exp2);
    assert power(base, exp1 + exp2) == power(base, exp1) * power(base, exp2);
  }
}

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
  PowerDivisionLemma(m - i);
  var p := power(2, m - i - 1);
  calc {
    1900 * (m - i - 1) * p + 100 * (n - m) * (p - 1) + 1900 * p;
    ==
    1900 * p * (m - i - 1 + 1) + 100 * (n - m) * (p - 1);
    ==
    1900 * (m - i) * p + 100 * (n - m) * (p - 1);
    ==
    1900 * (m - i) * (power(2, m - i) / 2) + 100 * (n - m) * (power(2, m - i) / 2 - 1);
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
    // Each test case with bug takes 1900 ms and divides the problem
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

