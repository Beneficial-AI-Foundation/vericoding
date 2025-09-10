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
function gcd_properties(a: int, b: int): bool
  requires a > 0 && b >= 0
  decreases b
{
  if b == 0 then true
  else gcd_properties(b, a % b)
}

lemma lemma_gcd_is_divisor(a: int, b: int)
  requires a > 0 && b >= 0
  ensures exists k :: a == k * gcd(a,b)
  ensures exists k :: b == k * gcd(a,b)
  decreases b
{
  if b == 0 {
    // gcd(a,0) == a, so a = 1*a, and b = 0 = 0*a
    assert a == 1 * gcd(a,b);
    assert 0 == 0 * gcd(a,b);
  } else {
    lemma_gcd_is_divisor(b, a % b);
    var g := gcd(b, a % b);
    // g divides b and a % b
    // Since a % b = a - k*b for some k, then if g divides b and a % b, it must divide a.
    // So g divides a and b.
    var b_k: int := 0; // Initialize b_k
    var rem_k: int := 0; // Initialize rem_k
    if exists k_tmp :: b == k_tmp * g { b_k := k_tmp; } else { assert false; }
    if exists k_tmp :: a % b == k_tmp * g { rem_k := k_tmp; } else { assert false; }
    assert b == b_k * g;
    assert a % b == rem_k * g;
    assert a == (a / b) * b + (a % b);
    assert a == (a / b) * (b_k * g) + (rem_k * g);
    assert a == ((a / b) * b_k + rem_k) * g;
    assert g == gcd(a,b); // This is needed to connect gcd(b, a%b) to gcd(a,b)
  }
}

lemma lemma_gcd_divides_both(a: int, b: int, d: int)
  requires a > 0 && b >= 0 && d > 0
  requires a % d == 0 && b % d == 0
  ensures gcd(a,b) % d == 0
  decreases b
{
  if b == 0 {
    // gcd(a,0) == a. Since a % d == 0, then gcd(a,0) % d == 0.
    assert gcd(a,0) == a;
    assert (a % d == 0) ==> (gcd(a,0) % d == 0);
  } else {
    lemma_gcd_divides_both(b, a % b, d);
    // gcd(a,b) == gcd(b, a % b).
    // If d divides b and a % b, then d divides gcd(b, a % b).
    assert gcd(a,b) == gcd(b, a % b);
    // We have (b % d == 0) and ((a % b) % d == 0) from the recursive call.
    // This isn't implicitly given, we need to prove (a % b) % d == 0 first.
    // a % d == 0 implies a = k1 * d
    // b % d == 0 implies b = k2 * d
    // a % b = a - (a / b) * b = k1 * d - (a / b) * k2 * d = (k1 - (a / b) * k2) * d
    // So (a % b) % d == 0.
    assert (a % b) % d == 0 by {
        var k_a := a / d;
        var k_b := b / d;
        assert a == k_a * d;
        assert b == k_b * d;
        assert a - (a / b) * b == k_a * d - (a / b) * (k_b * d);
        assert a - (a / b) * b == (k_a - (a / b) * k_b) * d;
    }
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
    var commonDivisor := gcd(A, B);
    // lemma_gcd_is_divisor(A, B); // This lemma is not needed for the postcondition.
    result := countDistinctPrimeFactors(commonDivisor) + 1;
}
// </vc-code>

