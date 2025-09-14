// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): added reads clause to allow array access */
predicate NoOccurrence(nums: array<int>, target: int) reads nums { forall i :: 0 <= i < nums.Length ==> nums[i] != target }

/* helper modified by LLM (iteration 2): added reads clause to allow array access */
predicate FoundAt(nums: array<int>, target: int, idx: int) reads nums { 0 <= idx < nums.Length && nums[idx] == target && forall j :: 0 <= j < idx ==> nums[j] != target }

/* helper modified by LLM (iteration 2): utility index validity function */
function IndexValid(idx: int, nums: array<int>): bool { 0 <= idx < nums.Length }
// </vc-helpers>

// <vc-spec>
method LinearSearch(nums: array<int>, target: int) returns (ret: int)
    requires nums.Length < 0x8000_0000
    ensures ret < nums.Length
    ensures ret >= 0 ==> nums[ret] == target
    ensures ret >= 0 ==> forall i :: 0 <= i < ret ==> nums[i] != target
    ensures ret < 0 ==> forall i :: 0 <= i < nums.Length ==> nums[i] != target
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): straightforward linear search implementation */
  var i := 0;
  while i < nums.Length
    invariant 0 <= i <= nums.Length
    invariant forall j :: 0 <= j < i ==> nums[j] != target
    decreases nums.Length - i
  {
    if nums[i] == target {
      return i;
    }
    i := i + 1;
  }
  return -1;
}
// </vc-code>
