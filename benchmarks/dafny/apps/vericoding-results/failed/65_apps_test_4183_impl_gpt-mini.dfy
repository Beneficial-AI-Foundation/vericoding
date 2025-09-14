function gcd(a: int, b: int): int
  requires a > 0 && b >= 0
  ensures gcd(a, b) > 0
  ensures gcd(a, b) <= a
  ensures b > 0 ==> gcd(a, b) <= b
  decreases b
{
  if b == 0 then a else gcd(b, a % b)
}

function lcm(a: int, b: int): int
  requires a > 0 && b > 0
  ensures lcm(a, b) >= a && lcm(a, b) >= b
  ensures lcm(a, b) > 0
{
  (a * b) / gcd(a, b)
}

function lcmSeq(nums: seq<int>): int
  requires |nums| > 0
  requires forall i :: 0 <= i < |nums| ==> nums[i] > 0
  ensures lcmSeq(nums) > 0
  ensures forall i :: 0 <= i < |nums| ==> lcmSeq(nums) >= nums[i]
{
  if |nums| == 1 then nums[0]
  else lcm(nums[0], lcmSeq(nums[1..]))
}

predicate ValidInput(periods: seq<int>)
{
  |periods| > 0 && |periods| <= 100 &&
  forall i :: 0 <= i < |periods| ==> periods[i] > 0
}

predicate CorrectResult(periods: seq<int>, result: int)
  requires ValidInput(periods)
{
  result == lcmSeq(periods)
}

// <vc-helpers>
lemma div_of_mul_equals(p: int, s: int, d: int)
  requires d > 0
  requires p == s * d
  ensures p / d == s
  ensures p % d == 0
{
  var q := p / d;
  var r := p % d;
  assert q * d + r == p;
  assert 0 <= r;
  assert r < d;

  // (q - s) * d + r == 0
  var t := q - s;
  assert t * d + r == 0;

  if t > 0 {
    // then t*d >= d > r, so t*d + r > 0, contradiction
    assert t * d >= d;
    assert t * d > r;
    assert 0 < 0;
  } else if t < 0 {
    // then t*d <= -d < 0 <= r, so t*d + r < 0, contradiction
    assert t * d <= -d;
    assert t * d < r;
    assert 0 < 0;
  } else {
    // t == 0, so r == 0 and q == s
    assert t == 0;
    assert r == 0;
    assert q == s;
  }
}

lemma divides_mul(d: int, k: int, b: int)
  requires d > 0
  requires b % d == 0
  ensures (k * b) % d == 0
{
  var q := b / d;
  // b == q*d + b%d and b%d == 0, so b == q*d
  assert q * d + b % d == b;
  assert b % d == 0;
  assert b == q * d;

  // k*b == (k*q) * d, so apply div_of_mul_equals
  var p := k * b;
  var s := k * q;
  assert p == s * d;
  div_of_mul_equals(p, s, d);
  // from div_of_mul_equals we get p % d == 0, i.e., (k*b) % d == 0
}

lemma div_mul_cancel(x: int, g: int)
  requires g > 0
  requires x >= 0
  ensures (x * g) / g == x
{
  var q := (x * g) / g;
  var r := (x * g) % g;
  // q*g + r == x*g and 0 <= r < g
  assert q * g + r == x * g;
  assert 0 <= r;
  assert r < g;

  var t := x - q;
  // (x - q) * g == r
  assert t * g + q * g == x * g;
  assert t * g == r;

  if t > 0 {
    // then t*g >= g > r, contradiction
    assert t * g >= g;
    assert t * g > r;
    assert 0 < 0;
  } else if t < 0 {
    // then t*g <= -g < 0 <= r, contradiction
    assert t * g <= -g;
    assert t * g < r;
    assert 0 < 0;
  } else {
    // t == 0 so q == x
    assert t == 0;
    assert q == x;
  }
}

lemma mul_div_pos(z: int, x: int, y: int)
  requires y > 0
  requires x % y == 0
  requires z >= 0
  ensures (z * x) / y == z * (x / y)
{
  var k := x / y;
  assert x == k * y;
  assert z * x == (z * k) * y;
  div_mul_cancel(z * k, y);
  assert (z * x) / y == z * k;
}

lemma gcd_divides(a: int, b: int)
  requires a > 0 && b >= 0
  ensures a %
// </vc-helpers>

// <vc-spec>
method FindMinimumTime(periods: seq<int>) returns (result: int)
  requires ValidInput(periods)
  ensures CorrectResult(periods, result)
// </vc-spec>
// <vc-code>
lemma div_of_mul_equals(p: int, s: int, d: int)
  requires d > 0
  requires p == s * d
  ensures p / d == s
  ensures p % d == 0
{
  var q := p / d;
  var r := p % d;
  assert q * d + r == p;
  assert 0 <= r;
  assert r < d;

  // (q - s) * d + r == 0
  var t := q - s;
  assert t * d + r == 0;

  if t > 0 {
    // then t*d >= d > r, so t*d + r > 0, contradiction
    assert t * d >= d;
    assert t * d > r;
    assert 0 < 0;
  } else if t < 0 {
    // then t*d <= -d < 0 <= r, so t*d + r < 0, contradiction
    assert t * d <= -d;
    assert t * d < r;
    assert 0 < 0;
  } else {
    // t == 0, so r == 0 and q == s
    assert t == 0;
    assert r == 0;
    assert q == s;
  }
}

lemma divides_mul(d: int, k: int, b: int)
  requires d > 0
  requires b % d == 0
  ensures (k * b) % d == 0
{
  var q := b / d;
  // b == q*d + b%d and b%d == 0, so b == q*d
  assert q * d + b % d == b;
  assert b % d == 0;
  assert b == q * d;

  // k*b == (k*q) * d, so apply div_of_mul_equals
  var p := k * b;
  var s := k * q;
  assert p == s * d;
  div_of_mul_equals(p, s, d);
  // from div_of_mul_equals we get p % d == 0, i.e., (k*b) % d == 0
}

lemma div_mul_cancel(x: int, g: int)
  requires g > 0
  requires x >= 0
  ensures (x * g) / g == x
{
  var q := (x * g) / g;
  var r := (x * g) % g;
  // q*g + r == x*g and 0 <= r < g
  assert q * g + r == x * g;
  assert 0 <= r;
  assert r < g;

  var t := x - q;
  // (x - q) * g == r
  assert t * g + q * g == x * g;
  assert t * g == r;

  if t > 0 {
    // then t*g >= g > r, contradiction
    assert t * g >= g;
    assert t * g > r;
    assert 0 < 0;
  } else if t < 0 {
    // then t*g <= -g < 0 <= r, contradiction
    assert t * g <= -g;
    assert t * g < r;
    assert 0 < 0;
  } else {
    // t == 0 so q == x
    assert t == 0;
    assert q == x;
  }
}

lemma mul_div_pos(z: int, x: int, y: int)
  requires y > 0
  requires x % y == 0
  requires z >= 0
  ensures (z * x) / y == z * (x / y)
{
  var k := x / y;
  assert x == k * y;
  assert z * x == (z * k) * y;
  div_mul_cancel(z * k, y);
  assert (z * x) / y == z * k;
}

lemma gcd_divides(a: int, b: int)
  requires a > 0 && b >= 0
  ensures a %
// </vc-code>

