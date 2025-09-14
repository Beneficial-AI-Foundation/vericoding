// <vc-preamble>
// Helper function to count occurrences of an element in a sequence
function CountOccurrences(nums: seq<int>, x: int): nat
{
    |set i | 0 <= i < |nums| && nums[i] == x|
}

// Helper function to filter elements equal to x (recursive implementation)
function FilterEqual(nums: seq<int>, x: int): seq<int>
{
    if |nums| == 0 then []
    else if nums[0] == x then [nums[0]] + FilterEqual(nums[1..], x)
    else FilterEqual(nums[1..], x)
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): construct index witness for membership and derive non-empty occurrence set */
lemma ExistsIndexForMember(nums: seq<int>, x: int)
  requires x in nums
  ensures exists i :: 0 <= i < |nums| && nums[i] == x
{
  if |nums| == 0 {
    // impossible due to requires
  } else {
    if nums[0] == x {
      assert exists i :: 0 <= i < |nums| && nums[i] == x;
    } else {
      ExistsIndexForMember(nums[1..], x);
      var j :| 0 <= j < |nums[1..]| && nums[1..][j] == x;
      assert 0 <= j + 1 < |nums|;
      assert nums[j + 1] == x;
      assert exists i :: 0 <= i < |nums| && nums[i] == x;
    }
  }
}

/* helper modified by LLM (iteration 4): show CountOccurrences >= 1 implies membership */
lemma CountOccurrences_positive_implies_member(nums: seq<int>, x: int)
  requires CountOccurrences(nums, x) >= 1
  ensures x in nums
{
  assert CountOccurrences(nums, x) == |set k | 0 <= k < |nums| && nums[k] == x|;
  assert CountOccurrences(nums, x) >= 1;
  assert |set k | 0 <= k < |nums| && nums[k] == x| >= 1;
  var k :| 0 <= k < |nums| && nums[k] == x;
  assert nums[k] == x;
  assert x in nums;
}

// </vc-helpers>

// <vc-spec>
method FindSingleNumber(nums: array<int>) returns (result: int)
    requires 
        nums.Length > 0
    requires
        exists unique_elem :: CountOccurrences(nums[..], unique_elem) == 1
    requires
        forall elem :: elem in nums[..] ==> (CountOccurrences(nums[..], elem) == 1 || CountOccurrences(nums[..], elem) == 2)
    ensures
        CountOccurrences(nums[..], result) == 1
    ensures
        forall x :: x in nums[..] ==> (x == result || CountOccurrences(nums[..], x) == 2)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 4): iterate to find element with single occurrence and return it */
  var found := false;
  var i := 0;
  while i < nums.Length && !found
    decreases nums.Length - i
  {
    if CountOccurrences(nums[..], nums[i]) == 1 {
      result := nums[i];
      found := true;
    }
    i := i + 1;
  }
  if !found {
    // Use existence precondition to obtain a value with single occurrence
    var v: int :| CountOccurrences(nums[..], v) == 1;
    // get an index where v occurs
    var idx: int :| 0 <= idx < nums.Length && nums[idx] == v;
    result := nums[idx];
  }
}

// </vc-code>
