

// <vc-helpers>
lemma NoSolutionContradiction(nums: array<int>, target: int, ii: int)
  requires 0 <= ii <= nums.Length
  requires ii == nums.Length - 1
  requires forall ii0,jj0 :: 0 <= ii0 < ii && ii0 < jj0 < nums.Length ==> nums[ii0] + nums[jj0] != target
  requires exists p,q :: 0 <= p < q < nums.Length && nums[p] + nums[q] == target
  ensures false
{
  var p, q :| 0 <= p < q < nums.Length && nums[p] + nums[q] == target;
  if p < ii {
    // instantiate the universal assumption to get a contradiction
    assert nums[p] + nums[q] != target;
    assert nums[p] + nums[q] == target;
    assert false;
  } else {
    // p >= ii and ii == nums.Length - 1 implies p == nums.Length - 1
    assert p >= ii;
    assert ii == nums.Length - 1;
    assert p < nums.Length;
    assert p >= nums.Length - 1;
    assert p == nums.Length - 1;
    // then q > p implies q >= nums.Length, contradicting q < nums.Length
    assert q > p;
    assert q >= nums.Length;
    assert q < nums.Length;
    assert false;
  }
}
// </vc-helpers>

// <vc-spec>
method twoSum(nums: array<int>, target: int) returns (i: int, j: int)
  requires nums.Length > 1
  requires exists i,j::0 <= i < j < nums.Length &&  nums[i] + nums[j] == target
  ensures 0 <= i < j < nums.Length && nums[i] + nums[j] == target
  ensures forall ii,jj:: (0 <= ii < i && ii < jj < nums.Length)  ==> nums[ii] + nums[jj] != target
  ensures forall jj:: i < jj < j ==> nums[i] + nums[jj] != target
// </vc-spec>
// <vc-code>
{
  var ii := 0;
  while ii < nums.Length - 1
    invariant 0 <= ii <= nums.Length - 1
    invariant forall ii0,jj0 :: 0 <= ii0 < ii && ii0 < jj0 < nums.Length ==> nums[ii0] + nums[jj0] != target
    decreases nums.Length - ii
  {
    var jj := ii + 1;
    while jj < nums.Length
      invariant 0 <= ii < nums.Length
      invariant ii < jj <= nums.Length
      invariant forall jj0 :: ii < jj0 < jj ==> nums[ii] + nums[jj0] != target
      invariant forall ii0,jj0 :: 0 <= ii0 < ii && ii0 < jj0 < nums.Length ==> nums[ii0] + nums[jj0] != target
      decreases nums.Length - jj
    {
      if nums[ii] + nums[jj] == target {
        i := ii;
        j := jj;
        return;
      }
      jj := jj + 1;
    }
    ii := ii + 1;
  }
  NoSolutionContradiction(nums, target, ii);
  assert false;
}
// </vc-code>

