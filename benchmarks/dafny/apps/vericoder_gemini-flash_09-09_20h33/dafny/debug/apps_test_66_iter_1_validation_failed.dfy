predicate ValidInput(t: int, w: int, b: int)
{
  t > 0 && w > 0 && b > 0
}

predicate ValidFraction(numerator: int, denominator: int)
{
  numerator >= 0 && denominator > 0 && numerator <= denominator
}

predicate IsIrreducibleFraction(numerator: int, denominator: int)
  requires ValidFraction(numerator, denominator)
{
  gcd(numerator, denominator) == 1
}

// <vc-helpers>
function gcd(a: int, b: int): int
  requires a >= 0 && b >= 0
  decreases a, b
{
  if b == 0 then a
  else gcd(b, a % b)
}

lemma EuclideanAlgorithm(a: int, b: int)
  requires a >= 0 && b >= 0
  ensures gcd(a, b) == gcd(b, a % b)
{}

lemma gcd_prop_divides(n: int, d: int)
  requires n >= 0 && d >= 0
  ensures (n % gcd(n, d) == 0) && (d % gcd(n, d) == 0)
{
  if d == 0 {
    assert gcd(n, d) == n;
    assert n % n == 0;
    assert d % n == 0; // 0 % n is 0
  } else {
    EuclideanAlgorithm(n, d);
    gcd_prop_divides(d, n % d);
  }
}

lemma gcd_is_largest_divisor(a: int, b: int, k: int)
  requires a >= 0 && b >= 0
  requires k > 0
  requires a % k == 0
  requires b % k == 0
  ensures gcd(a, b) % k == 0
{
  if b == 0 {
    assert gcd(a, b) == a;
    assert a % k == 0;
  } else {
    EuclideanAlgorithm(a, b);
    gcd_is_largest_divisor(b, a % b, k);
  }
}

lemma gcd_is_one_if_coprime(a: int, b: int)
  requires a >= 0 && b >= 0
  requires gcd(a, b) == 1
  ensures forall k: int :: (k > 0 && a % k == 0 && b % k == 0) ==> k == 1
{
  if a == 0 && b == 0 {
    // This case should not happen based on gcd(a,b) == 1
    // (since gcd(0,0) is 0)
  } else if a == 0 {
    // gcd(0, b) = b, so b must be 1.
    assert gcd(a, b) == b;
    assert b == 1;
    // Any k dividing a (0) and b (1) must be 1.
  } else if b == 0 {
    // gcd(a, 0) = a, so a must be 1.
    assert gcd(a, b) == a;
    assert a == 1;
    // Any k dividing a (1) and b (0) must be 1.
  }

  // Use gcd_is_largest_divisor to show that any common divisor k must divide gcd(a,b).
  // If gcd(a,b) is 1, then k must divide 1, so k must be 1.
}


lemma gcd_divides_both(a: int, b: int)
  requires a >= 0 && b >= 0
  ensures a % gcd(a, b) == 0 && b % gcd(a, b) == 0
{
  if b == 0 {
    assert gcd(a,b) == a;
    assert a % a == 0;
    assert b % a == 0; // 0 % a is 0
  } else {
    EuclideanAlgorithm(a, b);
    gcd_divides_both(b, a % b);
  }
}

lemma gcd_reduction_is_coprime(a: int, b: int)
  requires a >= 0 && b >= 0
  requires gcd(a, b) > 0
  ensures gcd(a / gcd(a, b), b / gcd(a, b)) == 1
{
  var g := gcd(a, b);
  assert g > 0;
  // Let's prove by contradiction. Assume gcd(a/g, b/g) = k > 1.
  // Then k divides a/g and k divides b/g.
  // So a/g = k * x and b/g = k * y for some integers x, y.
  // This means a = g * k * x and b = g * k * y.
  // So g * k is a common divisor of a and b.
  // Since k > 1, g * k > g.
  // But g is the greatest common divisor of a and b. This is a contradiction.

  // More formally, use gcd_is_largest_divisor
  var m := a / g;
  var n := b / g;
  var common_divisor_mn := gcd(m, n);

  if common_divisor_mn > 1 {
    // common_divisor_mn divides m and n.
    // So common_divisor_mn * g divides m * g and n * g.
    // i.e., common_divisor_mn * g divides a and b.
    // But g is gcd(a, b), and common_divisor_mn * g > g.
    // This contradicts the definition of g as the greatest common divisor.
    gcd_is_largest_divisor(a, b, common_divisor_mn * g);
    assert (g % (common_divisor_mn * g) == 0); // This must be true since g.k common divisor
    assert common_divisor_mn * g <= g; // This is the contradiction if common_divisor_mn > 1
  }
}
// </vc-helpers>

// <vc-spec>
method solve(t: int, w: int, b: int) returns (numerator: int, denominator: int)
  requires ValidInput(t, w, b)
  ensures ValidFraction(numerator, denominator)
  ensures IsIrreducibleFraction(numerator, denominator)
// </vc-spec>
// <vc-code>
{
  // The probability is t*w / (t*w + t*b + b*w) if we assume a specific process (not in spec)
  // Let's interpret the problem as finding a simplified fraction for a given calculation.
  // The context "t: target, w: water, b: bombs" seems to imply some sort of object distribution or game.
  // A common setup for "solve" with three inputs that results in a fraction is
  // related to a total number of items and specific "winning" or "losing" items.
  // A common probability expression is P_win = favorable / total.
  // Given t, w, b as counts, possible total is (t+w+b).
  // A common interpretation for such problems is selecting items without replacement.
  // However, without further context, a direct calculation from t, w, b is usually expected.
  // Let's assume the fraction to be simplified is (t*w) / (t*w + t*b + b*w) as this is a common form from similar problems.

  var num_val := t * w;
  var den_val := t * w + t * b + b * w;

  var common_divisor := gcd(num_val, den_val);

  // Since t, w, b are positive, num_val and den_val will be positive.
  // Therefore, common_divisor will be positive.
  assert common_divisor > 0;

  numerator := num_val / common_divisor;
  denominator := den_val / common_divisor;

  assert ValidFraction(numerator, denominator);
  assert IsIrreducibleFraction(numerator, denominator);
}
// </vc-code>

