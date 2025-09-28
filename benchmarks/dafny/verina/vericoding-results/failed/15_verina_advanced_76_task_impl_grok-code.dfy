// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method TopKFrequent(nums: array<int>, k: nat) returns (result: array<int>)
    requires k <= |set i | 0 <= i < nums.Length :: nums[i]|
    ensures result.Length == k
    ensures forall x :: x in result[..] ==> x in nums[..]
    ensures forall i, j :: 0 <= i < j < result.Length ==> result[i] != result[j]
// </vc-spec>
// <vc-code>
{
/* code modified by LLM (iteration 5): Fixed sequence length access from .Length to |unique| to resolve compilation errors */
  var seen: set<int> := {};
  var unique: seq<int> := [];
  var i := 0;
  while i < nums.Length
    invariant 0 <= i <= nums.Length
    invariant |seen| == |unique|
    invariant forall q :: 0 <= q < |unique| ==> unique[q] in nums[..] && unique[q] in seen
    invariant forall p, q :: 0 <= p < q < |unique| ==> unique[p] != unique[q]
  {
    if nums[i] !in seen {
      seen := seen + {nums[i]};
      unique := unique + [nums[i]];
    }
    i := i + 1;
  }
  assert k <= |set i | 0 <= i < nums.Length :: nums[i]|;
  assert k <= |unique|;
  result := new int[k];
  var j := 0;
  while j < k
    invariant 0 <= j <= k <= |unique|
    invariant forall q :: 0 <= q < j ==> result[q] == unique[q]
  {
    result[j] := unique[j];
    j := j + 1;
  }
}
// </vc-code>
