// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): added concrete proof of transitivity to avoid using quantifier statements and silence warnings */
lemma LeTransLtToLe(x: int, y: int, z: int)
  ensures (x <= y && y < z) ==> x <= z
{
  if x <= y && y < z {
    assert x <= y;
    assert y < z;
    assert x <= z;
  }
}
// </vc-helpers>

// <vc-spec>
method MaxArray(nums: array<int>) returns (idx: int)
    requires
        nums.Length >= 1
    ensures
        0 <= idx && idx < nums.Length &&
        forall i :: 0 <= i && i < nums.Length ==> nums[i] <= nums[idx]
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 3): removed forall-statement in proof to avoid warnings; rely on invariant preservation */
  idx := 0;
  var i := 1;
  while i < nums.Length
    invariant 0 <= idx && idx < i && i <= nums.Length
    invariant forall k :: 0 <= k && k < i ==> nums[k] <= nums[idx]
    decreases nums.Length - i
  {
    if nums[i] > nums[idx] {
      idx := i;
    }
    i := i + 1;
  }
}
// </vc-code>
