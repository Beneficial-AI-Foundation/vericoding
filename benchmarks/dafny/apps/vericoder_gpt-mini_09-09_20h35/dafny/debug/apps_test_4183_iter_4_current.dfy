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
lemma divides_mul(d: int, k: int, b: int)
  requires d > 0
  requires b % d == 0
  ensures (k * b) % d == 0
{
  var t := b / d;
  assert b == t * d;
  assert k * b == k * t * d;
  assert (k * b) % d == 0;
}

lemma div_mul_cancel(x: int, g: int)
  requires g > 0
  ensures (x * g) / g == x
{
  // x*g is an exact multiple of g, so division yields x
  assert (x * g) / g == x;
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
  ensures a % gcd(a, b) == 0 && b % gcd(a, b) == 0
  decreases b
{
  if b == 0 {
    assert gcd(a, b) == a;
    assert a % gcd(a, b) == 0;
    assert b % gcd(a, b) == 0;
  } else {
    // recursion on smaller second argument
    gcd_divides(b, a % b);
    assert gcd(a, b) == gcd(b, a % b);
    var d := gcd(a, b);
    // from recursive call we have:
    assert b % d == 0;
    assert (a % b) % d == 0;

    // write a = (a / b) * b + a % b
    var q := a / b;
    assert a == q * b + a % b;

    // (q * b) % d == 0 because b % d == 0
    divides_mul(d, q, b);
    assert (q * b) % d == 0;

    // then a % d == 0 because both summands are 0 mod d
    // from a == q*b + a%b we get a % d == (q*b + a%b) % d == 0
    assert a % d == 0;
  }
}

lemma lcm_correct(a: int, b: int)
  requires a > 0 && b > 0
  ensures lcm(a, b) >= a && lcm(a, b) >= b && lcm(a, b) > 0
{
  var g := gcd(a, b);
  gcd_divides(a, b);
  assert a % g == 0;
  assert b % g == 0;

  var ag := a / g;
  var bg := b / g;
  assert a == ag * g;
  assert b == bg * g;

  // lcm(a,b) == (a*b)/g
  assert lcm(a, b) == (a * b) / g;

  // a*b == a * (b/g) * g
  assert a * b == a * bg * g;
  // so (a*b)/g == (a*bg*g)/g == a*bg
  div_mul_cancel(a * bg, g);
  assert (a * bg * g) / g == a * bg;
  assert lcm(a, b) == a * bg;

  // show >= a: bg >= 1 because g <= b and b > 0
  assert g <= b;
  assert bg >= 1;
  assert a * bg >= a;

  // show >= b: ag >= 1 because g <= a
  assert g <= a;
  assert ag >= 1;
  // a*bg == ag*b, so since ag >= 1 we get >= b
  assert a * bg == ag * b;
  assert a * bg >= b;

  // positivity
  assert lcm(a, b) > 0;
}
// </vc-helpers>

// <vc-spec>
method FindMinimumTime(periods: seq<int>) returns (result: int)
  requires ValidInput(periods)
  ensures CorrectResult(periods, result)
// </vc-spec>
// <vc-code>
{
  var n := |periods|;
  if n == 1 {
    result := periods[0];
    return;
  }
  var i := n - 1;
  var acc := periods[i];
  // acc corresponds to lcmSeq(periods[i..])
  while i > 0
    invariant 0 <= i && i < n
    invariant acc > 0
    invariant acc == lcmSeq(periods[i..])
    decreases i
  {
    var oldAcc := acc;
    // oldAcc == lcmSeq(periods[i..]) by invariant
    i := i - 1;
    // now oldAcc == lcmSeq(periods[i+1..])
    assert oldAcc == lcmSeq(periods[i+1..]);
    var a := periods[i];
    var newAcc := lcm(a, oldAcc);
    // by definition of lcmSeq for slices of length >= 2:
    // lcmSeq(periods[i..]) == lcm(periods[i], lcmSeq(periods[i+1..]))
    assert newAcc == lcmSeq(periods[i..]);
    lcm_correct(a, oldAcc);
    acc := newAcc;
  }
  result := acc;
}
// </vc-code>

