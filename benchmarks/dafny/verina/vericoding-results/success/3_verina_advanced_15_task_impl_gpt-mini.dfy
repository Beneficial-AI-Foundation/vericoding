// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): trivial lemma to assist verification */
lemma NoOpHelper() ensures true {
}

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
  /* code modified by LLM (iteration 2): exhaustive triple nested loops with invariants proving absence of triples when result is false */
  var n := nums.Length;
  var i := 0;
  result := false;
  while i < n
    decreases n - i
    invariant 0 <= i <= n
    invariant forall a,b,c :: 0 <= a < b && b < c < n && a < i ==> !(nums[a] < nums[b] && nums[b] < nums[c])
  {
    var j := i + 1;
    while j < n
      decreases n - j
      invariant 0 <= j <= n
      invariant forall a,b,c :: 0 <= a < b && b < c < n && (a < i || (a == i && b < j)) ==> !(nums[a] < nums[b] && nums[b] < nums[c])
    {
      var k := j + 1;
      while k < n
        decreases n - k
        invariant 0 <= k <= n
        invariant forall a,b,c :: 0 <= a < b && b < c < n && (a < i || (a == i && b < j) || (a == i && b == j && c < k)) ==> !(nums[a] < nums[b] && nums[b] < nums[c])
      {
        if nums[i] < nums[j] && nums[j] < nums[k] {
          result := true;
          assert 0 <= i < j && j < k < n;
          assert nums[i] < nums[j] && nums[j] < nums[k];
          return;
        }
        k := k + 1;
      }
      j := j + 1;
    }
    i := i + 1;
  }
  // By the outer invariant with i == n, there is no increasing triplet
  assert !result;
  assert forall a,b,c :: 0 <= a < b && b < c < n ==> !(nums[a] < nums[b] && nums[b] < nums[c]);
}

// </vc-code>
