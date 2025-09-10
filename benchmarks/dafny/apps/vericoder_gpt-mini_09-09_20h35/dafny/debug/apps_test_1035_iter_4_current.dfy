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
lemma DividesFractionSmaller(n: int, factor: int)
  requires n > 0 && factor > 1
  ensures n / factor < n
{
  // n = (n / factor) * factor + n % factor
  assert (n / factor) * factor + n % factor == n;
  if n % factor == 0 {
    // then (n / factor) * factor == n, with factor > 1 implies n / factor < n
    assert (n / factor) * factor == n;
    // factor > 1 and (n / factor) * factor == n imply n / factor < n
    if n / factor >= n {
      // contradiction: (n / factor) * factor >= n * factor >= n * 2 > n
      assert (n / factor) * factor >= n * factor;
      assert n * factor > n;
      assert false;
    }
    assert n / factor < n;
  } else {
    // when n % factor != 0, (n / factor) * factor < n, hence n / factor < n
    assert (n / factor) * factor < n;
    if !(n / factor < n) {
      assert false;
    }
  }
}

lemma divideOutFactorShrinks(n: int, factor: int)
  requires n > 0 && factor > 1 && n % factor == 0
  ensures divideOutFactor(n, factor) < n
{
  var next := n / factor;
  if next % factor == 0 {
    // induction on the recursive structure
    divideOutFactorShrinks(next, factor);
    // from induction: divideOutFactor(next,factor) < next
    assert divideOutFactor(next, factor) < next;
    // and next < n
    DividesFractionSmaller(n, factor);
    assert next < n;
    // hence divideOutFactor(next,factor) < n
    assert divideOutFactor(next, factor) < n;
  } else {
    // base: returned value is next = n / factor, which is < n
    DividesFractionSmaller(n, factor);
    assert n / factor < n;
  }
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
  result := countDistinctPrimeFactors(gcd(A, B)) + 1;
}
// </vc-code>

