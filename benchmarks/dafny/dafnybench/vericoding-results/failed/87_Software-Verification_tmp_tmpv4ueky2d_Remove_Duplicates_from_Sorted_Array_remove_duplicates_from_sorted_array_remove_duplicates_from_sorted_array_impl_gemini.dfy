// <vc-preamble>
predicate is_sorted(nums: seq<int>)
{
    forall i, j :: 0 <= i < j < |nums| ==> nums[i] <= nums[j]
}

predicate is_sorted_and_distinct(nums: seq<int>)
{
    forall i, j :: 0 <= i < j < |nums| ==> nums[i] < nums[j]
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method remove_duplicates_from_sorted_array(nums: seq<int>) returns (result: seq<int>) 
    requires is_sorted(nums)
    requires 1 <= |nums| <= 30000
    requires forall i :: 0 <= i < |nums| ==> -100 <= nums[i] <= 100
    ensures is_sorted_and_distinct(result)
    ensures forall i :: i in nums <==> i in result
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): fixed compilation error by using set() constructor */
  result := [nums[0]];
  var i := 1;
  while i < |nums|
    invariant 1 <= i <= |nums|
    invariant is_sorted(nums)
    invariant is_sorted_and_distinct(result)
    invariant set(result) == set(nums[0..i])
    invariant forall x :: x in result ==> x in nums[0..i]
    invariant result[|result|-1] <= nums[i-1]
    invariant |result| >= 1 && result[0] == nums[0]
  {
    if nums[i] > result[|result|-1] {
      result := result + [nums[i]];
    }
    i := i + 1;
  }
}
// </vc-code>
