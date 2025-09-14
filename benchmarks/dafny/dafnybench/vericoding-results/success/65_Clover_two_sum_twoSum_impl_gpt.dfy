

// <vc-helpers>
// no helpers needed
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
  var n := nums.Length;
  var ii := 0;
  while ii < n
    invariant 0 <= ii <= n
    invariant forall i0, j0 :: 0 <= i0 < ii && i0 < j0 < n ==> nums[i0] + nums[j0] != target
    decreases n - ii
  {
    var jj := ii + 1;
    while jj < n && nums[ii] + nums[jj] != target
      invariant ii + 1 <= jj <= n
      invariant forall k :: ii < k < jj ==> nums[ii] + nums[k] != target
      decreases n - jj
    {
      jj := jj + 1;
    }
    if jj < n {
      i := ii;
      j := jj;
      return;
    }
    ii := ii + 1;
  }
  var wi, wj :| 0 <= wi < wj < n && nums[wi] + nums[wj] == target;
  assert ii == n;
  assert 0 <= wi;
  assert wi < ii;
  assert wj < n;
  assert nums[wi] + nums[wj] != target;
  assert nums[wi] + nums[wj] == target;
  assert false;
}
// </vc-code>

