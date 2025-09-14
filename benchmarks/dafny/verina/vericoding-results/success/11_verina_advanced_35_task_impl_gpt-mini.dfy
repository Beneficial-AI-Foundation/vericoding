// <vc-preamble>
function CountOccurrences(nums: seq<int>, x: int): nat
    decreases |nums|
{
    if |nums| == 0 then
        0
    else
        var first := nums[0];
        var restCount := CountOccurrences(nums[1..], x);
        if first == x then
            restCount + 1
        else
            restCount
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): existence of an index for any positive occurrence */
lemma OccurrenceImpliesIndex(nums: seq<int>, x: int)
  ensures CountOccurrences(nums, x) > 0 ==> exists i :: 0 <= i < |nums| && nums[i] == x
  decreases |nums|
{
  if |nums| == 0 {
  } else {
    var first := nums[0];
    var rest := nums[1..];
    if first == x {
      if CountOccurrences(nums, x) > 0 {
        assert 0 < |nums|;
        assert nums[0] == x;
        assert exists i :: 0 <= i < |nums| && nums[i] == x;
      }
    } else {
      if CountOccurrences(nums, x) > 0 {
        OccurrenceImpliesIndex(rest, x);
        var j :| 0 <= j < |rest| && rest[j] == x;
        var i := j + 1;
        assert 0 <= i < |nums|;
        assert nums[i] == x;
        assert exists k :: 0 <= k < |nums| && nums[k] == x;
      }
    }
  }
}

/* helper modified by LLM (iteration 2): sum of occurrences of two distinct values is <= length */
lemma CountSumLeqLength(nums: seq<int>, a: int, b: int)
  requires a != b
  ensures CountOccurrences(nums, a) + CountOccurrences(nums, b) <= |nums|
  decreases |nums|
{
  if |nums| == 0 {
  } else {
    var first := nums[0];
    var rest := nums[1..];
    CountSumLeqLength(rest, a, b);
    if first == a {
      assert CountOccurrences(nums, a) == CountOccurrences(rest, a) + 1;
      assert CountOccurrences(nums, b) == CountOccurrences(rest, b);
      assert CountOccurrences(nums, a) + CountOccurrences(nums, b) == CountOccurrences(rest, a) + CountOccurrences(rest, b) + 1;
      assert CountOccurrences(rest, a) + CountOccurrences(rest, b) + 1 <= |rest| + 1;
      assert CountOccurrences(nums, a) + CountOccurrences(nums, b) <= |nums|;
    } else if first == b {
      assert CountOccurrences(nums, a) == CountOccurrences(rest, a);
      assert CountOccurrences(nums, b) == CountOccurrences(rest, b) + 1;
      assert CountOccurrences(nums, a) + CountOccurrences(nums, b) == CountOccurrences(rest, a) + CountOccurrences(rest, b) + 1;
      assert CountOccurrences(rest, a) + CountOccurrences(rest, b) + 1 <= |rest| + 1;
      assert CountOccurrences(nums, a) + CountOccurrences(nums, b) <= |nums|;
    } else {
      assert CountOccurrences(nums, a) == CountOccurrences(rest, a);
      assert CountOccurrences(nums, b) == CountOccurrences(rest, b);
      assert CountOccurrences(nums, a) + CountOccurrences(nums, b) <= |nums|;
    }
  }
}

/* helper modified by LLM (iteration 2): majority is unique */
lemma MajorityUnique(nums: seq<int>, a: int, b: int)
  requires CountOccurrences(nums, a) > |nums| / 2 && CountOccurrences(nums, b) > |nums| / 2
  ensures a == b
{
  if a != b {
    CountSumLeqLength(nums, a, b);
    assert CountOccurrences(nums, a) + CountOccurrences(nums, b) <= |nums|;
    assert CountOccurrences(nums, a) + CountOccurrences(nums, b) > |nums|;
    assert false;
  }
}

/* helper modified by LLM (iteration 3): majority element implies uniqueness */
lemma MajorityImpliesUnique(nums: seq<int>, m: int)
  requires CountOccurrences(nums, m) > |nums| / 2
  ensures forall x :: x != m ==> CountOccurrences(nums, x) <= |nums| / 2
{
  if exists x :: x != m && CountOccurrences(nums, x) > |nums| / 2 {
    var x :| x != m && CountOccurrences(nums, x) > |nums| / 2;
    MajorityUnique(nums, m, x);
    assert false;
  }
}

// </vc-helpers>

// <vc-spec>
method MajorityElement(nums: seq<int>) returns (result: int)
    requires 
        |nums| > 0 &&
        exists x :: CountOccurrences(nums, x) > |nums| / 2
    ensures 
        CountOccurrences(nums, result) > |nums| / 2 &&
        forall x :: x != result ==> CountOccurrences(nums, x) <= |nums| / 2
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 3): linear scan returns when finds majority, otherwise use witness from precondition and apply uniqueness lemma */
  var n := |nums|;
  var i := 0;
  while i < n
    decreases n - i
    invariant 0 <= i <= n
    invariant forall k :: 0 <= k < i ==> CountOccurrences(nums, nums[k]) <= n / 2
  {
    var cand := nums[i];
    if CountOccurrences(nums, cand) > n / 2 {
      MajorityImpliesUnique(nums, cand);
      result := cand;
      return;
    } else {
      i := i + 1;
    }
  }
  var maj :| CountOccurrences(nums, maj) > n / 2;
  MajorityImpliesUnique(nums, maj);
  result := maj;
}

// </vc-code>
