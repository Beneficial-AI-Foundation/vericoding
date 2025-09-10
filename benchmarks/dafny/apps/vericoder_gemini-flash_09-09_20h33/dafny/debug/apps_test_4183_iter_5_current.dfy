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
function LcmSeqHelper(nums: seq<int>): int
  requires |nums| > 0
  requires forall i :: 0 <= i < |nums| ==> nums[i] > 0
  ensures LcmSeqHelper(nums) > 0
  ensures forall i :: 0 <= i < |nums| ==> LcmSeqHelper(nums) % nums[i] == 0
  decreases |nums|
{
  if |nums| == 1 then nums[0]
  else
    var tailLcm := LcmSeqHelper(nums[1..]);
    var currentLcm := lcm(nums[0], tailLcm);
    currentLcm
}
// </vc-helpers>

// <vc-spec>
method FindMinimumTime(periods: seq<int>) returns (result: int)
  requires ValidInput(periods)
  ensures CorrectResult(periods, result)
// </vc-spec>
// <vc-code>
{
  result := LcmSeqHelper(periods);
  assert result == lcmSeq(periods) by {
    if |periods| == 1 {
      assert LcmSeqHelper(periods) == periods[0];
      assert lcmSeq(periods) == periods[0];
    } else {
      assert LcmSeqHelper(periods[1..]) == lcmSeq(periods[1..]);
      assert lcm(periods[0], LcmSeqHelper(periods[1..])) == lcm(periods[0], lcmSeq(periods[1..]));
    }
  }
}
// </vc-code>

