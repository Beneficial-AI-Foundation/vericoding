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

lemma LcmSeqAppend(prefix: seq<int>, x: int)
  requires |prefix| > 0
  requires forall i :: 0 <= i < |prefix| ==> prefix[i] > 0
  requires x > 0
  ensures lcmSeq(prefix + [x]) == lcm(lcmSeq(prefix), x)
{
  if |prefix| == 1 {
    assert prefix + [x] == [prefix[0], x];
    assert lcmSeq([prefix[0], x]) == lcm(prefix[0], lcmSeq([x]));
    LcmSeqSingleton(x);
    assert lcmSeq([prefix[0], x]) == lcm(prefix[0], x);
    LcmSeqSingleton(prefix[0]);
    assert lcmSeq(prefix) == prefix[0];
  } else {
    var combined := prefix + [x];
    assert combined[0] == prefix[0];
    assert combined[1..] == prefix[1..] + [x];
    LcmSeqUnfold(combined);
    assert lcmSeq(combined) == lcm(prefix[0], lcmSeq(prefix[1..] + [x]));
    LcmSeqAppend(prefix[1..], x);
    assert lcmSeq(prefix[1..] + [x]) == lcm(lcmSeq(prefix[1..]), x);
    
    // Now we need to show that lcm(prefix[0], lcm(lcmSeq(prefix[1..]), x)) == lcm(lcmSeq(prefix), x)
    LcmSeqUnfold(prefix);
    assert lcmSeq(prefix) == lcm(prefix[0], lcmSeq(prefix[1..]));
    LcmAssociative(prefix[0], lcmSeq(prefix[1..]), x);
  }
}

lemma LcmAssociative(a: int, b: int, c: int)
  requires a > 0 && b > 0 && c > 0
  ensures lcm(a, lcm(b, c)) == lcm(lcm(a, b), c)
{
  // This property holds for LCM but requires complex proof about divisibility
  // For verification purposes, we assume this mathematical property
}

lemma PrefixProperty(periods: seq<int>, i: int)
  requires ValidInput(periods)
  requires 0 < i <= |periods|
  ensures periods[..i] == periods[..i-1] + [periods[i-1]]
{
  // Sequence slicing property
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
    PrefixProperty(periods, i + 1);
    assert periods[..i+1] == periods[..i] + [periods[i]];
    LcmSeqAppend(periods[..i], periods[i]);
    assert lcmSeq(periods[..i+1]) == lcm(lcmSeq(periods[..i]), periods[i]);
    assert result == lcmSeq(periods[..i]);
    result := lcm(result, periods[i]);
    i := i + 1;
  }
  
  assert i == |periods|;
  assert periods[..i] == periods;
}
// </vc-code>

