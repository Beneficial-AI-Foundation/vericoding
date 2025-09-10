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
// (No helpers needed)
// </vc-helpers>

// <vc-spec>
method solve(A: int, B: int) returns (result: int)
  requires ValidInput(A, B)
  ensures result > 0
  ensures CorrectResult(A, B, result)
// </vc-spec>
// <vc-code>
{
  var x := A;
  var y := B;
  while y != 0
    invariant x > 0 && y >= 0
    invariant gcd(x, y) == gcd(A, B)
    decreases y
  {
    assert y > 0;
    var t := x % y;
    x := y;
    y := t;
  }
  assert y == 0;
  assert gcd(x, 0) == x;
  assert gcd(A, B) == x;
  result := countDistinctPrimeFactors(x) + 1;
}
// </vc-code>

