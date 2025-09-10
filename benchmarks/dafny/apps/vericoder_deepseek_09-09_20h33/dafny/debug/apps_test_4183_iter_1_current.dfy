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
// </vc-helpers>

// <vc-spec>
method FindMinimumTime(periods: seq<int>) returns (result: int)
  requires ValidInput(periods)
  ensures CorrectResult(periods, result)
// </vc-spec>
// <vc-code>
{
  var result := 1;
  var i := 0;
  
  while i < |periods|
    invariant 0 <= i <= |periods|
    invariant result > 0
    invariant forall j :: 0 <= j < i ==> result % periods[j] == 0
    invariant result % lcmSeq(periods[0..i]) == 0
    invariant lcmSeq(periods[0..i]) % result == 0
  {
    if result % periods[i] != 0 {
      result := lcm(result, periods[i]);
    }
    i := i + 1;
  }
}
// </vc-code>

