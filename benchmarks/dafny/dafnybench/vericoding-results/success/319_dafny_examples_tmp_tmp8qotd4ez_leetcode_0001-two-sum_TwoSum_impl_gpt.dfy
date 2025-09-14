// If this invariant is added explicitly to the loop then the verfication never finishes.
// It could be {:opaque} for a more controlled verification:
// assert InMap([], m, target) by {
//   reveal InMap();
// }
predicate InMap(nums: seq<int>, m: map<int, int>, t: int) {
  forall j :: 0 <= j < |nums| ==> t - nums[j] in m
}

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method TwoSum(nums: array<int>, target: int) returns (r: (int, int))
  ensures 0 <= r.0 ==> 0 <= r.0 < r.1 < nums.Length && 
                       nums[r.0] + nums[r.1] == target &&
                       forall i, j :: 0 <= i < j < r.1 ==> nums[i] + nums[j] != target
  ensures r.0 == -1 <==> forall i, j :: 0 <= i < j < nums.Length ==> nums[i] + nums[j] != target
// </vc-spec>
// <vc-code>
{
  var n := nums.Length;
  var j := 0;
  while j < n
    invariant 0 <= j <= n
    invariant forall a:int, b:int :: 0 <= a < b < j ==> nums[a] + nums[b] != target
  {
    var i := 0;
    while i < j
      invariant 0 <= i <= j
      invariant forall a:int :: 0 <= a < i ==> nums[a] + nums[j] != target
      invariant forall a:int, b:int :: 0 <= a < b < j ==> nums[a] + nums[b] != target
    {
      if nums[i] + nums[j] == target {
        r := (i, j);
        return;
      }
      i := i + 1;
    }
    j := j + 1;
  }
  r := (-1, -1);
}
// </vc-code>

