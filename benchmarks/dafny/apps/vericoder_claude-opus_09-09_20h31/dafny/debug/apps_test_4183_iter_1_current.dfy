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
lemma LcmSeqUnfold(nums: seq<int>)
  requires |nums| >= 2
  requires forall i :: 0 <= i < |nums| ==> nums[i] > 0
  ensures lcmSeq(nums) == lcm(nums[0], lcmSeq(nums[1..]))
{
  // By definition of lcmSeq
}

lemma LcmSeqSingleton(x: int)
  requires x > 0
  ensures lcmSeq([x]) == x
{
  // By definition of lcmSeq
}

lemma LcmSeqPrefix(nums: seq<int>, k: int)
  requires |nums| > 0
  requires 0 < k <= |nums|
  requires forall i :: 0 <= i < |nums| ==> nums[i] > 0
  ensures k == 1 ==> lcmSeq(nums[..k]) == nums[0]
  ensures k > 1 ==> lcmSeq(nums[..k]) == lcm(lcmSeq(nums[..k-1]), nums[k-1])
{
  if k == 1 {
    assert nums[..1] == [nums[0]];
    LcmSeqSingleton(nums[0]);
  } else {
    assert nums[..k] == nums[..k-1] + [nums[k-1]];
    if k == 2 {
      assert nums[..1] == [nums[0]];
      LcmSeqSingleton(nums[0]);
      assert lcmSeq(nums[..2]) == lcm(nums[0], lcmSeq([nums[1]]));
      LcmSeqSingleton(nums[1]);
      assert lcmSeq(nums[..2]) == lcm(nums[0], nums[1]);
      assert lcmSeq(nums[..1]) == nums[0];
      assert lcmSeq(nums[..2]) == lcm(lcmSeq(nums[..1]), nums[1]);
    } else {
      var prefix := nums[..k-1];
      assert |prefix| >= 1;
      assert forall i :: 0 <= i < |prefix| ==> prefix[i] > 0;
      assert nums[..k] == prefix + [nums[k-1]];
      assert lcmSeq(nums[..k]) == lcmSeq(prefix + [nums[k-1]]);
      
      if |prefix| == 1 {
        assert prefix == [nums[0]];
        assert lcmSeq(prefix + [nums[k-1]]) == lcm(nums[0], lcmSeq([nums[k-1]]));
        LcmSeqSingleton(nums[k-1]);
        assert lcmSeq(prefix + [nums[k-1]]) == lcm(nums[0], nums[k-1]);
        assert lcmSeq(prefix) == nums[0];
      } else {
        assert |prefix| > 1;
        assert lcmSeq(prefix + [nums[k-1]]) == lcm(prefix[0], lcmSeq((prefix + [nums[k-1]])[1..]));
        assert (prefix + [nums[k-1]])[1..] == prefix[1..] + [nums[k-1]];
      }
    }
  }
}

lemma LcmSeqFullEqualsPrefix(nums: seq<int>)
  requires |nums| > 0
  requires forall i :: 0 <= i < |nums| ==> nums[i] > 0
  ensures lcmSeq(nums) == lcmSeq(nums[..|nums|])
{
  assert nums == nums[..|nums|];
}
// </vc-helpers>

// <vc-spec>
method FindMinimumTime(periods: seq<int>) returns (result: int)
  requires ValidInput(periods)
  ensures CorrectResult(periods, result)
// </vc-spec>
// <vc-code>
{
  result := periods[0];
  var i := 1;
  
  while i < |periods|
    invariant 1 <= i <= |periods|
    invariant result == lcmSeq(periods[..i])
    invariant result > 0
  {
    LcmSeqPrefix(periods, i + 1);
    result := lcm(result, periods[i]);
    i := i + 1;
  }
  
  assert i == |periods|;
  assert periods[..i] == periods[..|periods|];
  assert periods[..|periods|] == periods;
  assert result == lcmSeq(periods);
}
// </vc-code>

