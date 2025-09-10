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
ghost predicate Divides(d : int, n : int)
{
  n % d == 0
}

lemma GcdDivides(a: int, b: int)
  requires a > 0 && b >= 0
  ensures Divides(gcd(a,b), a) && Divides(gcd(a,b), b)
  decreases b
{
  if b == 0 {
  } else {
    GcdDivides(b, a % b);
    var a1 := a / b;
    var rem := a % b;
    assert a == b * a1 + rem;
    var d := gcd(a,b);
    var db := b;
    assert Divides(d, db);
    var drem := a % b;
    assert Divides(d, drem);
    assert Divides(d, a1 * db + drem);
  }
}

lemma LCMProperties(a: int, b: int)
  requires a > 0 && b > 0
  ensures lcm(a,b) >= a
  ensures lcm(a,b) >= b
{
  GcdDivides(a, b);
  var d := gcd(a,b);
  assert d > 0;
  var m := b / d;
  assert m >= 1;
  assert lcm(a,b) == a * m;
  assert a * m >= a;
  var k := a / d;
  assert k >= 1;
  assert lcm(a,b) == b * k;
  assert b * k >= b;
}
// </vc-helpers>

// <vc-spec>
method FindMinimumTime(periods: seq<int>) returns (result: int)
  requires ValidInput(periods)
  ensures CorrectResult(periods, result)
// </vc-spec>
// <vc-code>
{
  return lcmSeq(periods);
}
// </vc-code>

