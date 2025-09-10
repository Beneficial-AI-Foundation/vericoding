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
lemma gcd_divides(a: int, b: int)
  requires a > 0 && b >= 0
  ensures a % gcd(a, b) == 0 && b % gcd(a, b) == 0
  decreases b
{
  if b == 0 {
    // gcd(a,0) == a, so a % a == 0 and 0 % a == 0
  } else {
    gcd_divides(b, a % b);
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
  assert z * x == z * k * y;
  assert (z * x) / y == (z * k * y) / y;
  // since y > 0 and (z*k*y) is an exact multiple of y, division yields z*k
  assert (z * k * y) / y == z * k;
}

lemma lcm_correct(a: int, b: int)
  requires a > 0 && b > 0
  ensures lcm(a, b) >= a && lcm(a, b) >= b && lcm(a, b) > 0
{
  var g := gcd(a, b);
  // g divides a and b
  gcd_divides(a, b);
  // (a*b)/g == a*(b/g)
  mul_div_pos(a, b, g);
  assert (a * b) / g == a * (b / g);
  // b/g >= 1 because g <= b and b > 0
  assert b / g >= 1;
  assert a * (b / g) >= a;
  assert (a * b) / g >= a;

  // similarly, (a*b)/g == b*(a/g)
  mul_div_pos(b, a, g);
  assert (a * b) / g == b * (a / g);
  assert a / g >= 1;
  assert b * (a / g) >= b;
  assert (a * b) / g >= b;

  // positivity
  assert (a * b) / g > 0;
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
    i := i - 1;
    var a := periods[i];
    var newAcc := lcm(a, oldAcc);
    lcm_correct(a, oldAcc);
    acc := newAcc;
    // By definition of lcmSeq, for the slice periods[i..] (length >= 2 here)
    // lcmSeq(periods[i..]) == lcm(periods[i], lcmSeq(periods[i+1..])) and
    // oldAcc == lcmSeq(periods[i+1..]) by the loop invariant before the decrement,
    // so acc == lcmSeq(periods[i..]) holds.
  }
  result := acc;
}
// </vc-code>

