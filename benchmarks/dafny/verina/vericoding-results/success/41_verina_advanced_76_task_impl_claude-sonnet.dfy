// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function CountOccurrences(nums: array<int>, x: int): nat
  reads nums
{
  |set i | 0 <= i < nums.Length && nums[i] == x|
}

function GetUniqueElements(nums: array<int>): set<int>
  reads nums
{
  set i | 0 <= i < nums.Length :: nums[i]
}

/* helper modified by LLM (iteration 4): added initialization and verification logic */
method FindMostFrequent(nums: array<int>, excluded: set<int>) returns (element: int)
  requires nums.Length > 0
  requires |GetUniqueElements(nums) - excluded| > 0
  ensures element in GetUniqueElements(nums)
  ensures element !in excluded
  ensures forall x :: x in GetUniqueElements(nums) && x !in excluded ==> CountOccurrences(nums, element) >= CountOccurrences(nums, x)
{
  var i := 0;
  while i < nums.Length && nums[i] in excluded
    invariant 0 <= i <= nums.Length
    invariant forall j :: 0 <= j < i ==> nums[j] in excluded
  {
    i := i + 1;
  }
  
  element := nums[i];
  var maxCount := CountOccurrences(nums, element);
  
  for j := i + 1 to nums.Length
    invariant element in GetUniqueElements(nums)
    invariant element !in excluded
    invariant maxCount == CountOccurrences(nums, element)
    invariant forall x :: x in GetUniqueElements(nums) && x !in excluded && x in (set k | 0 <= k < j :: nums[k]) ==> CountOccurrences(nums, element) >= CountOccurrences(nums, x)
  {
    if nums[j] !in excluded {
      var count := CountOccurrences(nums, nums[j]);
      if count > maxCount {
        maxCount := count;
        element := nums[j];
      }
    }
  }
}
// </vc-helpers>

// <vc-spec>
method TopKFrequent(nums: array<int>, k: nat) returns (result: array<int>)
    requires k <= |set i | 0 <= i < nums.Length :: nums[i]|
    ensures result.Length == k
    ensures forall x :: x in result[..] ==> x in nums[..]
    ensures forall i, j :: 0 <= i < j < result.Length ==> result[i] != result[j]
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 4): improved loop invariants and element selection */
{
  if k == 0 {
    result := new int[0];
    return;
  }
  
  result := new int[k];
  var used: set<int> := {};
  
  for i := 0 to k
    invariant 0 <= i <= k
    invariant |used| == i
    invariant |GetUniqueElements(nums) - used| >= k - i
    invariant forall j :: 0 <= j < i ==> result[j] in GetUniqueElements(nums)
    invariant forall j :: 0 <= j < i ==> result[j] in used
    invariant forall j :: 0 <= j < i ==> result[j] !in used - {result[j]}
    invariant forall x, y :: 0 <= x < y < i ==> result[x] != result[y]
    invariant forall j :: 0 <= j < i ==> result[j] in nums[..]
  {
    var next := FindMostFrequent(nums, used);
    result[i] := next;
    used := used + {next};
  }
}
// </vc-code>
