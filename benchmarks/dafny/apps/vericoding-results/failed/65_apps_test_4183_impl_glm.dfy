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
lemma lcm_product_divisible(a: int, b: int)
  requires a > 0 && b > 0
  ensures (a * b) % gcd(a, b) == 0
{
  var g := gcd(a, b);
  assert a % g == 0;
  calc {
    (a * b) % g;
    ==  { assert (a * b) % g == (a % g * b) % g; }
    (0 * b) % g;
    ==  { }
    0 % g;
    ==  { }
    0;
  }
}

lemma lcm_positivity(a: int, b: int)
  requires a > 0 && b > 0
  ensures lcm(a, b) > 0
{
  calc {
    lcm(a, b);
    ==  { }
    (a * b) / gcd(a, b);
    >  0;
      { assert a * b > 0; assert gcd(a, b) > 0; }
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

