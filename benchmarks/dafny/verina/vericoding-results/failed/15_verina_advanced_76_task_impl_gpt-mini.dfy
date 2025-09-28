// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): PrefixSet for arrays */
function PrefixSet(nums: array<int>, i: nat): set<int>
  requires i <= nums.Length
{
  set j | 0 <= j < i :: nums[j]
}

/* helper modified by LLM (iteration 5): SuffixSet for arrays */
function SuffixSet(nums: array<int>, i: nat): set<int>
  requires i <= nums.Length
{
  set j | i <= j < nums.Length :: nums[j]
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
{
  /* code modified by LLM (iteration 5): collect first k distinct elements from nums into result using seen set and SuffixSet helper */
  result := new int[k];
  var seen: set<int> := {};
  var i := 0;
  var idx := 0;
  while i < nums.Length && idx < k
    invariant 0 <= i <= nums.Length
    invariant 0 <= idx <= k
    invariant forall v :: v in seen ==> (exists j :: 0 <= j < i && nums[j] == v)
    invariant idx == |seen|
    invariant forall p, q :: 0 <= p < q < idx ==> result[p] != result[q]
    invariant forall t :: 0 <= t < idx ==> result[t] in seen
    invariant idx + |SuffixSet(nums, i) - seen| >= k
    decreases nums.Length - i
  {
    var v := nums[i];
    if !(v in seen) {
      result[idx] := v;
      seen := seen + {v};
      idx := idx + 1;
    }
    i := i + 1;
  }
  assert idx == k;
}
// </vc-code>
