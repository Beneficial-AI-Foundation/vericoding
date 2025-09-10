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
lemma LcmSeqProperties(nums: seq<int>)
  requires |nums| > 0
  requires forall i :: 0 <= i < |nums| ==> nums[i] > 0
  ensures lcmSeq(nums) > 0
  ensures forall i :: 0 <= i < |nums| ==> lcmSeq(nums) >= nums[i]
{
  if |nums| == 1 {
    assert lcmSeq(nums) == nums[0];
  } else {
    LcmSeqProperties(nums[1..]);
    assert lcmSeq(nums) == lcm(nums[0], lcmSeq(nums[1..]));
  }
}

lemma GcdProperties(a: int, b: int)
  requires a > 0 && b >= 0
  ensures gcd(a, b) > 0
  ensures gcd(a, b) <= a
  ensures b > 0 ==> gcd(a, b) <= b
{
}

lemma GcdDivisibilityProperties(a: int, b: int)
  requires a > 0 && b > 0
  ensures a % gcd(a, b) == 0
  ensures b % gcd(a, b) == 0
  decreases b
{
  if b == 0 {
    assert gcd(a, b) == a;
    assert a % a == 0;
  } else if a % b > 0 {
    GcdDivisibilityProperties(b, a % b);
    var g := gcd(b, a % b);
    assert g == gcd(a, b);
    assert b % g == 0;
    assert (a % b) % g == 0;
    
    var q := a / b;
    assert a == q * b + (a % b);
    
    assert a % g == ((q * b + (a % b)) % g);
    assert a % g == (((q * b) % g) + ((a % b) % g)) % g;
    assert a % g == (0 + 0) % g;
    assert a % g == 0;
  } else {
    assert a % b == 0;
    assert gcd(a, b) == b;
    assert a % b == 0;
    assert b % b == 0;
  }
}

lemma LcmMathematicalProperties(a: int, b: int)
  requires a > 0 && b > 0
  ensures gcd(a, b) * lcm(a, b) == a * b
  ensures a % gcd(a, b) == 0
  ensures b % gcd(a, b) == 0
  ensures lcm(a, b) % a == 0
  ensures lcm(a, b) % b == 0
{
  var g := gcd(a, b);
  GcdDivisibilityProperties(a, b);
  assert g > 0;
  assert a % g == 0;
  assert b % g == 0;
  var lcm_val := (a * b) / g;
  assert lcm_val == lcm(a, b);
  
  var a_div := a / g;
  var b_div := b / g;
  assert a == g * a_div;
  assert b == g * b_div;
  assert lcm_val == (g * a_div * b) / g;
  assert lcm_val == a_div * b;
  assert lcm_val == (a / g) * b;
  assert g * lcm_val == g * ((a / g) * b);
  assert g * lcm_val == a * b;
}

lemma LcmProperties(a: int, b: int)
  requires a > 0 && b > 0
  ensures lcm(a, b) >= a && lcm(a, b) >= b
  ensures lcm(a, b) > 0
{
  GcdProperties(a, b);
  LcmMathematicalProperties(a, b);
}
// </vc-helpers>

// <vc-spec>
method FindMinimumTime(periods: seq<int>) returns (result: int)
  requires ValidInput(periods)
  ensures CorrectResult(periods, result)
// </vc-spec>
// <vc-code>
{
  result := lcmSeq(periods);
  LcmSeqProperties(periods);
}
// </vc-code>

