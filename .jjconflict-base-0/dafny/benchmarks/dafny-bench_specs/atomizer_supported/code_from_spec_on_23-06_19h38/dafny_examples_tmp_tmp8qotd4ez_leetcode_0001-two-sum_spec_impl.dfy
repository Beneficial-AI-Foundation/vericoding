//ATOM 
// If this invariant is added explicitly to the loop then the verfication never finishes.
// It could be {:opaque} for a more controlled verification:
// assert InMap([], m, target) by {
//   reveal InMap();
// }
predicate InMap(nums: seq<int>, m: map<int, int>, t: int) {
  forall j :: 0 <= j < |nums| ==> t - nums[j] in m
}

//IMPL 
method TwoSum(nums: array<int>, target: int) returns (r: (int, int))
  ensures 0 <= r.0 ==> 0 <= r.0 < r.1 < nums.Length && 
                       nums[r.0] + nums[r.1] == target &&
                       forall i, j :: 0 <= i < j < r.1 ==> nums[i] + nums[j] != target
  ensures r.0 == -1 <==> forall i, j :: 0 <= i < j < nums.Length ==> nums[i] + nums[j] != target
{
  var i := 0;
  while i < nums.Length
    invariant 0 <= i <= nums.Length
    /* code modified by LLM (iteration 4): invariant captures all pairs where first element index is less than i */
    invariant forall x, y :: 0 <= x < y < nums.Length && x < i ==> nums[x] + nums[y] != target
  {
    var j := i + 1;
    while j < nums.Length
      invariant i + 1 <= j <= nums.Length
      /* code modified by LLM (iteration 4): invariant for pairs with first element at index i and second element before j */
      invariant forall y :: i < y < j ==> nums[i] + nums[y] != target
      /* code modified by LLM (iteration 4): preserve outer loop invariant during inner loop */
      invariant forall x, y :: 0 <= x < y < nums.Length && x < i ==> nums[x] + nums[y] != target
    {
      if nums[i] + nums[j] == target {
        /* code modified by LLM (iteration 4): assert properties before return to help verification */
        assert 0 <= i < j < nums.Length;
        assert nums[i] + nums[j] == target;
        assert forall x, y :: 0 <= x < y < j && (x < i || (x == i && y < j)) ==> nums[x] + nums[y] != target;
        return (i, j);
      }
      j := j + 1;
    }
    i := i + 1;
  }
  /* code modified by LLM (iteration 4): assert final condition before return */
  assert forall x, y :: 0 <= x < y < nums.Length ==> nums[x] + nums[y] != target;
  return (-1, -1);
}