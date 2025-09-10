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
lemma PowerOfTwoIterative(m: int)
  requires 0 <= m
  ensures exists p :: p == power(2, m) && p == ComputePowerOfTwo(m)
{
  var p := ComputePowerOfTwo(m);
  assert p == power(2, m);
}

function ComputePowerOfTwo(m: int): int
  requires 0 <= m
  decreases m
{
  if m == 0 then 1 else 2 * ComputePowerOfTwo(m - 1)
}

lemma ComputePowerOfTwoCorrect(m: int)
  requires 0 <= m
  ensures ComputePowerOfTwo(m) == power(2, m)
{
  if m == 0 {
    assert ComputePowerOfTwo(0) == 1 == power(2, 0);
  } else {
    ComputePowerOfTwoCorrect(m - 1);
    assert ComputePowerOfTwo(m) == 2 * ComputePowerOfTwo(m - 1) == 2 * power(2, m - 1) == power(2, m);
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
  // Compute power(2, m) iteratively
  var p := 1;
  var i := 0;
  
  while i < m
    invariant 0 <= i <= m
    invariant p == power(2, i)
    invariant ValidInput(n, m)
  {
    p := p * 2;
    i := i + 1;
  }
  
  assert p == power(2, m);
  
  // Compute the formula: (1900 * m + 100 * (n - m)) * power(2, m)
  var coefficient := 1900 * m + 100 * (n - m);
  result := coefficient * p;
  
  assert result == (1900 * m + 100 * (n - m)) * power(2, m);
  assert result == ExpectedTime(n, m);
}
// </vc-code>

