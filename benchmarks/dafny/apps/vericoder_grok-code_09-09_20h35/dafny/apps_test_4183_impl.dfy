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
  requires d != 0
{
  n % d == 0
}

lemma GcdDivides(a: int, b: int)
  requires a > 0 && b >= 0
  ensures Divides(gcd(a,b), a) && Divides(gcd(a,b), b)
  decreases b
{
  if b == 0 {
    assert gcd(a,0) == a;
    assert a > 0 ==> Divides(a, a);
    assert b == 0 ==> true;
  } else {
    GcdDivides(b, a % b);
    assert a % b > 0 || a % b == 0;
    var d := gcd(a,b);
    assert Divides(d, b);
    var rem := a % b;
    assert Divides(gcd(b, rem), rem) && Divides(gcd(b, rem), b);
    assert gcd(b, rem) == d;
    assert Divides(d, rem);
    assert Divides(d, a / b * b + rem);
    assert Divides(d, a);
  }
}

lemma DividesProduct(d: int, a: int, b: int)
  requires d != 0
  requires Divides(d, a) && Divides(d, b)
  ensures Divides(d, a * b)
{
  var a1 := a / d;
  assert a == d * a1;
  var b1 := b / d;
  assert b == d * b1;
  assert a * b == d * (a1 * d * b1);
  assert a * b == d * (d * a1 * b1);
  assert Divides(d, d * (a1 * b1));
  assert Divides(d, a * b);
}

lemma LCMProperties(a: int, b: int)
  requires a > 0 && b > 0
  ensures lcm(a,b) >= a
  ensures lcm(a,b) >= b
{
  GcdDivides(a, b);
  DividesProduct(gcd(a,b), a, b);
  var d := gcd(a,b);
  assert Divides(d, a);
  assert Divides(d, b);
  assert Divides(d, a * b);
  var m := b / d;
  assert b == d * m;
  assert m > 0;
  assert lcm(a,b) == a * m;
  assert a * m >= a;
  var k := a / d;
  assert a == d * k;
  assert k > 0;
  assert lcm(a,b) == b * k;
  assert b * k >= b;
}

lemma LCMSeqEnsures(nums: seq<int>)
  requires |nums| > 0
  requires forall i :: 0 <= i < |nums| ==> nums[i] > 0
  ensures lcmSeq(nums) > 0
  ensures forall i :: 0 <= i < |nums| ==> lcmSeq(nums) >= nums[i]
  decreases nums
{
  if |nums| == 1 {
    assert lcmSeq(nums) == nums[0] > 0;
    assert nums[0] >= nums[0];
  } else {
    LCMSeqEnsures(nums[1..]);
    assert lcmSeq(nums[1..]) > 0;
    assert forall j :: 0 <= j < |nums[1..]| ==> lcmSeq(nums[1..]) >= nums[1..][j];
    LCMProperties(nums[0], lcmSeq(nums[1..]));
    assert lcm(nums[0], lcmSeq(nums[1..])) >= nums[0];
    assert lcm(nums[0], lcmSeq(nums[1..])) >= lcmSeq(nums[1..]);
  }
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

