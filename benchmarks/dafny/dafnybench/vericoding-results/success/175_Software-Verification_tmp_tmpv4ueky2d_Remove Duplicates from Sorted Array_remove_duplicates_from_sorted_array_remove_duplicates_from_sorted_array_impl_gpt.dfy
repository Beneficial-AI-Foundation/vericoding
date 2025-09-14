// Helper predicate
predicate is_sorted(nums: seq<int>)
{
    forall i, j :: 0 <= i < j < |nums| ==> nums[i] <= nums[j]
}

predicate is_sorted_and_distinct(nums: seq<int>)
{
    forall i, j :: 0 <= i < j < |nums| ==> nums[i] < nums[j]
}

// <vc-helpers>
function uniq(s: seq<int>): seq<int>
  ensures forall x :: x in s <==> x in uniq(s)
  ensures is_sorted(s) ==> is_sorted_and_distinct(uniq(s))
  ensures |s| > 0 ==> |uniq(s)| > 0 && uniq(s)[0] == s[0]
  decreases |s|
{
  if |s| <= 1 then s
  else if s[0] == s[1] then uniq(s[1..])
  else [s[0]] + uniq(s[1..])
}
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
  return uniq(nums);
}
// </vc-code>

