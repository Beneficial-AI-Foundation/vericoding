predicate ValidInput(A: int, B: int)
{
  A > 0 && B > 0
}

function gcd(a: int, b: int): int
  requires a > 0 && b >= 0
  ensures gcd(a, b) > 0
  decreases b
{
  if b == 0 then a else gcd(b, a % b)
}

function countDistinctPrimeFactors(n: int): int
  requires n > 0
  ensures countDistinctPrimeFactors(n) >= 0
{
  if n == 1 then 0
  else countDistinctPrimeFactorsHelper(n, 2)
}

function countDistinctPrimeFactorsHelper(n: int, i: int): int
  requires n > 0 && i >= 2
  ensures countDistinctPrimeFactorsHelper(n, i) >= 0
  decreases 2*n - i
{
  if i * i > n then
    if n > 1 then 1 else 0
  else if n % i == 0 then
    1 + countDistinctPrimeFactorsHelper(divideOutFactor(n, i), i + 1)
  else
    countDistinctPrimeFactorsHelper(n, i + 1)
}

function divideOutFactor(n: int, factor: int): int
  requires n > 0 && factor > 1 && n % factor == 0
  ensures divideOutFactor(n, factor) > 0
  ensures divideOutFactor(n, factor) < n
  ensures divideOutFactor(n, factor) % factor != 0
  decreases n
{
  var next := n / factor;
  if next % factor == 0 then divideOutFactor(next, factor) else next
}

predicate CorrectResult(A: int, B: int, result: int)
  requires A > 0 && B > 0
{
  result == countDistinctPrimeFactors(gcd(A, B)) + 1
}

// <vc-helpers>
method computeGcd(a: int, b: int) returns (result: int)
  requires a > 0 && b > 0
  ensures result > 0
  ensures result == gcd(a, b)
{
  var x, y := a, b;
  while y > 0
    invariant x > 0 && y >= 0
    invariant gcd(x, y) == gcd(a, b)
    decreases y
  {
    var temp := y;
    y := x % y;
    x := temp;
  }
  result := x;
}

method computeCountDistinctPrimeFactors(n: int) returns (count: int)
  requires n > 0
  ensures count >= 0
  ensures count == countDistinctPrimeFactors(n)
{
  if n == 1 {
    count := 0;
  } else {
    count := computeCountDistinctPrimeFactorsHelper(n, 2);
  }
}

method computeCountDistinctPrimeFactorsHelper(n: int, i: int) returns (count: int)
  requires n > 0 && i >= 2
  ensures count >= 0
  ensures count == countDistinctPrimeFactorsHelper(n, i)
  decreases 2*n - i
{
  if i * i > n {
    if n > 1 {
      count := 1;
    } else {
      count := 0;
    }
  } else if n % i == 0 {
    var divided := computeDivideOutFactor(n, i);
    var subCount := computeCountDistinctPrimeFactorsHelper(divided, i + 1);
    count := 1 + subCount;
  } else {
    count := computeCountDistinctPrimeFactorsHelper(n, i + 1);
  }
}

method computeDivideOutFactor(n: int, factor: int) returns (result: int)
  requires n > 0 && factor > 1 && n % factor == 0
  ensures result > 0
  ensures result < n
  ensures result % factor != 0
  ensures result == divideOutFactor(n, factor)
  decreases n
{
  var next := n / factor;
  assert next > 0;
  assert next < n;
  if next % factor == 0 {
    result := computeDivideOutFactor(next, factor);
  } else {
    result := next;
  }
}

lemma divideOutFactorCorrect(n: int, factor: int)
  requires n > 0 && factor > 1 && n % factor == 0
  ensures var next := n / factor; next > 0 && next < n
{
  var next := n / factor;
  assert n >= factor;
  assert next * factor == n;
  assert next >= 1;
  assert next < n;
}

lemma gcdPositive(a: int, b: int)
  requires a > 0 && b > 0
  ensures gcd(a, b) > 0
{
}

lemma countNonNegative(n: int)
  requires n > 0
  ensures countDistinctPrimeFactors(n) >= 0
{
}
// </vc-helpers>

// <vc-spec>
method solve(A: int, B: int) returns (result: int)
  requires ValidInput(A, B)
  ensures result > 0
  ensures CorrectResult(A, B, result)
// </vc-spec>
// <vc-code>
{
  gcdPositive(A, B);
  var g := computeGcd(A, B);
  countNonNegative(g);
  var count := computeCountDistinctPrimeFactors(g);
  result := count + 1;
}
// </vc-code>

