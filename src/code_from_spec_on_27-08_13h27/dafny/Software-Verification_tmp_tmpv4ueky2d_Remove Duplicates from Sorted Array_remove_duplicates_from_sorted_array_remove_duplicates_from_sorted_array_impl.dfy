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
// Helper lemma to prove properties about sequences
lemma SeqProperties(s: seq<int>, i: int)
  requires 0 <= i < |s|
  ensures s[i] in s
{
}

// Helper function to check if an element exists in a sequence up to a certain index
function contains_up_to(s: seq<int>, val: int, end: int): bool
  requires 0 <= end <= |s|
{
  exists i :: 0 <= i < end && s[i] == val
}

// Helper lemma to ensure uniqueness in a subsequence
lemma UniqueSubseq(s: seq<int>, sub: seq<int>)
  requires forall i, j :: 0 <= i < j < |sub| ==> sub[i] != sub[j]
  ensures forall i, j :: 0 <= i < j < |sub| ==> sub[i] != sub[j]
{
}

// Lemma to help prove that appending to a sorted distinct sequence maintains the property
lemma AppendMaintainsSortedDistinct(s: seq<int>, x: int)
  requires is_sorted_and_distinct(s)
  requires |s| > 0 ==> s[|s|-1] < x
  ensures is_sorted_and_distinct(s + [x])
{
  if |s| == 0 {
  } else {
    assert forall i :: 0 <= i < |s| ==> s[i] < x;
  }
}

// Lemma to prove all elements up to index i in nums are accounted for in result
lemma AllElementsAccounted(nums: seq<int>, res: seq<int>, i: int)
  requires 0 <= i <= |nums|
  requires is_sorted(nums)
  requires forall k :: 0 <= k < i && (k == 0 || nums[k] != nums[k-1]) ==> nums[k] in res
  requires forall k :: k in res ==> exists j :: 0 <= j < i && nums[j] == k
  ensures forall k :: contains_up_to(nums, k, i) <==> k in res
{
  if i == 0 {
    assert forall k :: !contains_up_to(nums, k, i);
    assert forall k :: k !in res;
  } else {
    var j := i - 1;
    if j == 0 || nums[j] != nums[j-1] {
      assert nums[j] in res;
    }
    assert forall k :: contains_up_to(nums, k, i) <==> contains_up_to(nums, k, j) || nums[j] == k;
    assert forall k :: k in res ==> exists m :: 0 <= m < i && nums[m] == k;
  }
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
method remove_duplicates_from_sorted_array(nums: seq<int>) returns (result: seq<int>) 
    requires is_sorted(nums)
    requires 1 <= |nums| <= 30000
    requires forall i :: 0 <= i < |nums| ==> -100 <= nums[i] <= 100
    ensures is_sorted_and_distinct(result)
    ensures forall i :: i in nums <==> i in result
// </vc-spec>
// </vc-spec>

// <vc-code>
method RemoveDuplicatesFromSortedArray(nums: seq<int>) returns (result: seq<int>)
  requires is_sorted(nums)
  requires 1 <= |nums| <= 30000
  requires forall i :: 0 <= i < |nums| ==> -100 <= nums[i] <= 100
  ensures is_sorted_and_distinct(result)
  ensures forall i :: i in nums <==> i in result
{
  if |nums| == 1 {
    return nums;
  }

  var res: seq<int> := [];
  var i := 0;

  while i < |nums|
    invariant 0 <= i <= |nums|
    invariant is_sorted_and_distinct(res)
    invariant forall k :: 0 <= k < i && (k == 0 || nums[k] != nums[k-1]) ==> nums[k] in res
    invariant forall k :: k in res ==> exists j :: 0 <= j < i && nums[j] == k
    decreases |nums| - i
  {
    if i == 0 || nums[i] != nums[i-1] {
      if |res| > 0 {
        assert i > 0;
        assert res[|res|-1] in res;
        assert exists j :: 0 <= j < i && nums[j] == res[|res|-1];
        var j :| 0 <= j < i && nums[j] == res[|res|-1];
        if j < i - 1 {
          assert nums[j] <= nums[i-1];
          if nums[j] == nums[i-1] {
            assert i > 1;
            assert nums[i-1] == nums[i-2];
            assert false;
          } else {
            assert nums[j] < nums[i-1];
            assert res[|res|-1] < nums[i];
          }
        } else {
          assert res[|res|-1] == nums[i-1];
        }
      }
      if |res| == 0 || res[|res|-1] < nums[i] {
        AppendMaintainsSortedDistinct(res, nums[i]);
        res := res + [nums[i]];
      }
    }
    i := i + 1;
  }

  result := res;
  AllElementsAccounted(nums, res, |nums|);
  assert forall k :: contains_up_to(nums, k, |nums|) <==> k in result;
}
// </vc-code>
