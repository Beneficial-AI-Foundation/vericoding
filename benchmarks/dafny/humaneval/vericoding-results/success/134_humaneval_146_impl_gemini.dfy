// <vc-preamble>

function FirstDigit(n: int): int
  requires n > 0
{
  if n < 10 then n else FirstDigit(n / 10)
}

function LastDigit(n: int): int
  requires n > 0
{
  n % 10
}

function IsOdd(n: int): bool
{
  n == 1 || n == 3 || n == 5 || n == 7 || n == 9
}

predicate SatisfiesCondition(n: int)
{
  n > 10 && IsOdd(FirstDigit(n)) && IsOdd(LastDigit(n))
}

predicate ValidInput(nums: seq<int>)
{
  true
}
function CountHelper(nums: seq<int>, index: int): int
  requires 0 <= index <= |nums|
  decreases |nums| - index
  ensures CountHelper(nums, index) >= 0
  ensures CountHelper(nums, index) <= |nums| - index
{
  if index == |nums| then 0
  else
    var current := nums[index];
    var contribution := if SatisfiesCondition(current) then 1 else 0;
    contribution + CountHelper(nums, index + 1)
}

lemma CountHelperCorrectness(nums: seq<int>, index: int)
  requires 0 <= index <= |nums|
  ensures CountHelper(nums, index) == |set i | index <= i < |nums| && SatisfiesCondition(nums[i])|
  decreases |nums| - index
{
  if index == |nums| {
    assert (set i | index <= i < |nums| && SatisfiesCondition(nums[i])) == {};
  } else {
    CountHelperCorrectness(nums, index + 1);
    var setWithIndex := set i | index <= i < |nums| && SatisfiesCondition(nums[i]);
    var setWithoutIndex := set i | index + 1 <= i < |nums| && SatisfiesCondition(nums[i]);

    if SatisfiesCondition(nums[index]) {
      assert setWithIndex == {index} + setWithoutIndex;
      assert index !in setWithoutIndex;
      assert |setWithIndex| == 1 + |setWithoutIndex|;
    } else {
      assert setWithIndex == setWithoutIndex;
    }
  }
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method SpecialFilter(nums: seq<int>) returns (count: int)
  requires ValidInput(nums)
  ensures count >= 0
  ensures count <= |nums|
  ensures count == |set i | 0 <= i < |nums| && SatisfiesCondition(nums[i])|
  ensures nums == [] ==> count == 0
  ensures forall i :: 0 <= i < |nums| && SatisfiesCondition(nums[i]) ==> nums[i] > 10 && IsOdd(FirstDigit(nums[i])) && IsOdd(LastDigit(nums[i]))
// </vc-spec>
// <vc-code>
{
  count := CountHelper(nums, 0);
  CountHelperCorrectness(nums, 0);
}
// </vc-code>
