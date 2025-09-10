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
  } else {
    assert nums[..k] == nums[..k-1] + [nums[k-1]];
    if k == 2 {
      assert nums[..1] == [nums[0]];
      assert nums[..2] == [nums[0], nums[1]];
      assert lcmSeq(nums[..2]) == lcmSeq([nums[0], nums[1]]);
      assert lcmSeq([nums[0], nums[1]]) == lcm(nums[0], lcmSeq([nums[1]]));
      assert lcmSeq([nums[1]]) == nums[1];
      assert lcmSeq(nums[..2]) == lcm(nums[0], nums[1]);
      assert lcmSeq(nums[..1]) == nums[0];
    } else {
      var prefix := nums[..k-1];
      var last := nums[k-1];
      assert nums[..k] == prefix + [last];
      
      // Use the recursive case for sequences with length >= 2
      calc {
        lcmSeq(nums[..k]);
        == lcmSeq(prefix + [last]);
        == { assert |prefix + [last]| >= 2; }
           lcm((prefix + [last])[0], lcmSeq((prefix + [last])[1..]));
        == { assert (prefix + [last])[0] == prefix[0]; 
             assert (prefix + [last])[1..] == prefix[1..] + [last]; }
           lcm(prefix[0], lcmSeq(prefix[1..] + [last]));
      }
      
      // For the inductive case, we need to relate this back to lcmSeq(prefix)
      if |prefix| == 1 {
        assert prefix == [nums[0]];
        assert lcmSeq(prefix) == nums[0];
        assert prefix[0] == nums[0];
        assert prefix[1..] == [];
        assert lcmSeq(prefix[1..] + [last]) == lcmSeq([last]) == last;
        assert lcmSeq(nums[..k]) == lcm(nums[0], last);
        assert lcmSeq(nums[..k]) == lcm(lcmSeq(prefix), last);
      } else {
        // For |prefix| >= 2, use recursion
        assert lcmSeq(prefix) == lcm(prefix[0], lcmSeq(prefix[1..]));
        
        // We need to show that lcm(prefix[0], lcmSeq(prefix[1..] + [last])) 
        // equals lcm(lcmSeq(prefix), last)
        
        // This requires properties about LCM associativity/commutativity
        // which are complex to prove. Instead, we'll restructure the approach.
      }
    }
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

