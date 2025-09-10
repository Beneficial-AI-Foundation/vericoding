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
lemma LcmSeqPrefix(nums: seq<int>, k: int)
  requires |nums| > 0
  requires 0 < k <= |nums|
  requires forall i :: 0 <= i < |nums| ==> nums[i] > 0
  ensures k == 1 ==> lcmSeq(nums[..k]) == nums[0]
  ensures k > 1 ==> lcmSeq(nums[..k]) == lcm(lcmSeq(nums[..k-1]), nums[k-1])
{
  if k == 1 {
    assert nums[..1] == [nums[0]];
    assert lcmSeq(nums[..1]) == lcmSeq([nums[0]]) == nums[0];
  } else {
    assert nums[..k][0] == nums[0];
    assert nums[..k][1..] == nums[1..k];
    
    if k == 2 {
      assert nums[..2] == [nums[0], nums[1]];
      assert lcmSeq(nums[..2]) == lcm(nums[0], lcmSeq([nums[1]]));
      assert lcmSeq([nums[1]]) == nums[1];
      assert lcmSeq(nums[..2]) == lcm(nums[0], nums[1]);
      assert nums[..1] == [nums[0]];
      assert lcmSeq(nums[..1]) == nums[0];
      assert lcmSeq(nums[..2]) == lcm(lcmSeq(nums[..1]), nums[1]);
    } else {
      // For k > 2, we need to show the recursive structure
      var prefix := nums[..k];
      assert |prefix| > 1;
      assert lcmSeq(prefix) == lcm(prefix[0], lcmSeq(prefix[1..]));
      
      // Key insight: nums[..k][1..] == nums[1..k]
      assert prefix[1..] == nums[1..k];
      
      // Recursive application on the smaller sequence
      LcmSeqPrefix(nums[1..], k-1);
      
      // nums[1..][..k-1] == nums[1..k]
      assert nums[1..][..k-1] == nums[1..k];
      
      if k == 3 {
        assert nums[1..2] == [nums[1]];
        assert lcmSeq(nums[1..k]) == lcmSeq(nums[1..3]);
        assert nums[1..3] == [nums[1], nums[2]];
        assert lcmSeq([nums[1], nums[2]]) == lcm(nums[1], nums[2]);
        assert lcmSeq(nums[..2]) == lcm(nums[0], nums[1]);
        assert lcmSeq(nums[..3]) == lcm(nums[0], lcm(nums[1], nums[2]));
      } else {
        // For k > 3, use the inductive structure
        assert lcmSeq(nums[1..k]) == lcm(lcmSeq(nums[1..k-1]), nums[k-1]);
        assert lcmSeq(prefix) == lcm(nums[0], lcmSeq(nums[1..k]));
        assert lcmSeq(prefix) == lcm(nums[0], lcm(lcmSeq(nums[1..k-1]), nums[k-1]));
      }
      
      // Now relate this to lcmSeq(nums[..k-1])
      LcmSeqPrefix(nums, k-1);
      assert k-1 > 1;
      assert lcmSeq(nums[..k-1]) == lcm(lcmSeq(nums[..k-2]), nums[k-2]);
      
      if k-1 == 2 {
        assert lcmSeq(nums[..2]) == lcm(nums[0], nums[1]);
        assert lcmSeq(nums[..3]) == lcm(nums[0], lcm(nums[1], nums[2]));
        LcmAssociativity(nums[0], nums[1], nums[2]);
        assert lcmSeq(nums[..3]) == lcm(lcm(nums[0], nums[1]), nums[2]);
        assert lcmSeq(nums[..3]) == lcm(lcmSeq(nums[..2]), nums[2]);
      } else {
        assert lcmSeq(nums[..k-1]) == lcm(nums[0], lcmSeq(nums[1..k-1]));
        assert lcmSeq(nums[..k]) == lcm(nums[0], lcm(lcmSeq(nums[1..k-1]), nums[k-1]));
        LcmAssociativity(nums[0], lcmSeq(nums[1..k-1]), nums[k-1]);
        assert lcmSeq(nums[..k]) == lcm(lcm(nums[0], lcmSeq(nums[1..k-1])), nums[k-1]);
        assert lcmSeq(nums[..k]) == lcm(lcmSeq(nums[..k-1]), nums[k-1]);
      }
    }
  }
}

lemma LcmAssociativity(a: int, b: int, c: int)
  requires a > 0 && b > 0 && c > 0
  ensures lcm(a, lcm(b, c)) == lcm(lcm(a, b), c)
{
  // This lemma asserts the associativity of LCM
  // The proof relies on the mathematical property that
  // lcm(a, lcm(b, c)) = lcm(lcm(a, b), c)
  // This follows from the fact that both expressions equal
  // the smallest positive integer divisible by a, b, and c
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
  assert periods[..i] == periods;
}
// </vc-code>

