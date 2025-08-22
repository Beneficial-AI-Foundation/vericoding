// If this invariant is added explicitly to the loop then the verfication never finishes.
// It could be {:opaque} for a more controlled verification:
// assert InMap([], m, target) by {
//   reveal InMap();
// }
//ATOM_PLACEHOLDER_InMap

//IMPL TwoSum
method TwoSum(nums: array<int>, target: int) returns (r: (int, int))
  ensures 0 <= r.0 ==> 0 <= r.0 < r.1 < nums.Length && 
                       nums[r.0] + nums[r.1] == target &&
                       forall i, j :: 0 <= i < j < r.1 ==> nums[i] + nums[j] != target
  ensures r.0 == -1 <==> forall i, j :: 0 <= i < j < nums.Length ==> nums[i] + nums[j] != target
{
  var i := 0;
  while i < nums.Length
    invariant 0 <= i <= nums.Length
    /* code modified by LLM (iteration 4): Invariant ensuring no valid pairs exist with second index less than or equal to i */
    invariant forall x, y :: 0 <= x < y <= i ==> nums[x] + nums[y] != target
  {
    var j := i + 1;
    while j < nums.Length
      invariant i + 1 <= j <= nums.Length
      /* code modified by LLM (iteration 4): Maintain outer invariant about pairs with second index less than or equal to i */
      invariant forall x, y :: 0 <= x < y <= i ==> nums[x] + nums[y] != target
      /* code modified by LLM (iteration 4): No valid pairs with first index i and second index less than j */
      invariant forall y :: i + 1 <= y < j ==> nums[i] + nums[y] != target
    {
      if nums[i] + nums[j] == target {
        /* code modified by LLM (iteration 4): Comprehensive assertion that this is the first valid pair */
        assert forall x, y :: 0 <= x < y <= i ==> nums[x] + nums[y] != target;
        assert forall y :: i + 1 <= y < j ==> nums[i] + nums[y] != target;
        assert forall x, y :: 0 <= x < y < j ==> nums[x] + nums[y] != target;
        return (i, j);
      }
      j := j + 1;
    }
    /* code modified by LLM (iteration 4): Assert that no valid pairs exist with first index i */
    assert forall y :: i + 1 <= y < nums.Length ==> nums[i] + nums[y] != target;
    i := i + 1;
  }
  /* code modified by LLM (iteration 4): Assert that no valid pairs exist in the entire array */
  assert forall x, y :: 0 <= x < y < nums.Length ==> nums[x] + nums[y] != target;
  return (-1, -1);
}