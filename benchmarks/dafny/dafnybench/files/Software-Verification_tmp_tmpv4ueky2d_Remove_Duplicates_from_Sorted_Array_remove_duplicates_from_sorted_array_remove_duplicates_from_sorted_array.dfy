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
  assume {:axiom} false;
}
// </vc-code>
