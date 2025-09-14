// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
lemma NoopLemma() { }
// </vc-helpers>

// <vc-spec>
method IncreasingTriplet(nums: array<int>) returns (result: bool)
    ensures
        result ==> exists i: int, j: int, k: int :: 
            0 <= i < j && j < k < nums.Length && 
            nums[i] < nums[j] && nums[j] < nums[k]
    ensures
        !result ==> forall i: int, j: int, k: int :: 
            0 <= i < j && j < k < nums.Length ==> 
            !(nums[i] < nums[j] && nums[j] < nums[k])
// </vc-spec>
// <vc-code>
{
  var n := nums.Length;
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant forall a,b,c :: 0 <= a && a < b && b < c && c < n && a < i ==> !(nums[a] < nums[b] && nums[b] < nums[c])
  {
    var j := i + 1;
    while j < n
      invariant i + 1 <= j <= n
      invariant forall b,c :: i < b && b < c && c < n && b < j ==> !(nums[i] < nums[b] && nums[b] < nums[c])
    {
      var k := j + 1;
      while k < n
        invariant j + 1 <= k <= n
        invariant forall c :: j < c && c < k ==> !(nums[i] < nums[j] && nums[j] < nums[c])
      {
        if nums[i] < nums[j] && nums[j] < nums[k] {
          result := true;
          return;
        }
        k := k + 1;
      }
      j := j + 1;
    }
    i := i + 1;
  }
  result := false;
}
// </vc-code>
