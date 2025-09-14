predicate distinct(nums: seq<int>) {
    forall i, j :: 0 <= i < j < |nums| ==> nums[i] != nums[j]
}

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method contains_duplicate(nums: seq<int>) returns (result: bool)
    requires 1 <= |nums| <= 100000
    requires forall i :: 0 <= i < |nums| ==> -1000000000 <= nums[i] <= 1000000000
    ensures result <==> distinct(nums)
// </vc-spec>
// <vc-code>
{
  var s: set<int> := {};
  var i := 0;
  while i < |nums|
    invariant 0 <= i <= |nums|
    invariant forall j :: 0 <= j < i ==> nums[j] !in (s - {nums[j]})
    invariant s == set k | 0 <= k < i :: nums[k]
    invariant distinct(nums[0..i])
  {
    if nums[i] in s {
      result := false;
      return;
    }
    s := s + {nums[i]};
    i := i + 1;
  }
  result := true;
}
// </vc-code>

