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
lemma {:induction false} LcmSeqLemma(nums: seq<int>)
  requires |nums| > 0
  requires forall i :: 0 <= i < |nums| ==> nums[i] > 0
  ensures lcmSeq(nums) > 0
  ensures forall i :: 0 <= i < |nums| ==> lcmSeq(nums) % nums[i] == 0
  decreases |nums|
{
  if |nums| != 1 {
    LcmSeqLemma(nums[1..]);
    DivisionLemma(nums[0], lcmSeq(nums[1..]));
  }
}

lemma DivisionLemma(a: int, b: int)
  requires a > 0 && b > 0
  ensures (a * b) / gcd(a, b) % a == 0
  ensures (a * b) / gcd(a, b) % b == 0
{
}

lemma LcmDivisible(a: int, b: int, x: int)
  requires a > 0 && b > 0 && x > 0
  requires x % a == 0 && x % b == 0
  ensures x % lcm(a, b) == 0
{
}

lemma LcmSeqDivisible(nums: seq<int>, x: int)
  requires |nums| > 0
  requires forall i :: 0 <= i < |nums| ==> nums[i] > 0
  requires forall i :: 0 <= i < |nums| ==> x % nums[i] == 0
  ensures x % lcmSeq(nums) == 0
  decreases |nums|
{
  if |nums| == 1 {
  } else {
    LcmSeqDivisible(nums[1..], x);
    LcmDivisible(nums[0], lcmSeq(nums[1..]), x);
  }
}

lemma LcmOfLcm(a: int, b: int, c: int)
  requires a > 0 && b > 0 && c > 0
  requires c % a == 0 && c % b == 0
  ensures lcm(a, b) <= c
{
}

lemma LcmSeqMonotonic(nums: seq<int>, i: int)
  requires |nums| > 0
  requires forall j :: 0 <= j < |nums| ==> nums[j] > 0
  requires 0 <= i < |nums|
  ensures lcmSeq(nums[0..i+1]) % lcmSeq(nums[0..i]) == 0
{
  if i > 0 {
    LcmSeqMonotonic(nums[0..i], i-1);
  }
}

lemma LcmResultInvariant(nums: seq<int>, i: int, res: int)
  requires |nums| > 0
  requires forall j :: 0 <= j < |nums| ==> nums[j] > 0
  requires 0 <= i <= |nums|
  requires res > 0
  requires forall j :: 0 <= j < i ==> res % nums[j] == 0
  requires res % lcmSeq(nums[0..i]) == 0
  requires lcmSeq(nums[0..i]) % res == 0
  ensures i < |nums| ==> lcm(res, nums[i]) % lcmSeq(nums[0..i+1]) == 0
  ensures i < |nums| ==> lcmSeq(nums[0..i+1]) % lcm(res, nums[i]) == 0
{
  if i < |nums| {
    var next_lcm := lcm(res, nums[i]);
    assert next_lcm % res == 0;
    assert next_lcm % nums[i] == 0;
    LcmSeqDivisible(nums[0..i+1], next_lcm);
    assert next_lcm % lcmSeq(nums[0..i+1]) == 0;
    
    var current_lcm := lcmSeq(nums[0..i]);
    assert lcmSeq(nums[0..i+1]) == lcm(nums[i], current_lcm);
    LcmOfLcm(res, nums[i], lcmSeq(nums[0..i+1]));
    assert lcmSeq(nums[0..i+1]) % next_lcm == 0;
  }
}
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
method FindMinimumTime(periods: seq<int>) returns (result: int)
  requires ValidInput(periods)
  ensures CorrectResult(periods, result)
// </vc-spec>
// <vc-code>
{
  var current := 1;
  var i := 0;
  
  while i < |periods|
    invariant 0 <= i <= |periods|
    invariant current > 0
    invariant forall j :: 0 <= j < i ==> current % periods[j] == 0
    invariant current % lcmSeq(periods[0..i]) == 0
    invariant lcmSeq(periods[0..i]) % current == 0
  {
    LcmResultInvariant(periods, i, current);
    if current % periods[i] != 0 {
      current := lcm(current, periods[i]);
    }
    i := i + 1;
  }
  result := current;
}
// </vc-code>
// </vc-code>

