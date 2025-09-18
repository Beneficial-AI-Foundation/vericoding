// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): provide min function */
function min(a: int, b: int): int { if a < b then a else b }

/* helper modified by LLM (iteration 2): trivial lemma that 0 is non-negative */
lemma ZeroNonNegative()
  ensures 0 <= 0
{
}

// </vc-helpers>

// <vc-spec>
method SemiOrderedPermutation(nums: array<int>) returns (result: int)
    ensures 
        result >= 0
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): count non-decreasing adjacent pairs; removed null check */
  var n := nums.Length;
  if n <= 1 {
    result := 0;
    return;
  }
  var cnt := 0;
  var i := 0;
  while i + 1 < n
    invariant 0 <= cnt
    invariant 0 <= i <= n
    invariant cnt <= i
  {
    if nums[i] <= nums[i+1] {
      cnt := cnt + 1;
    }
    i := i + 1;
  }
  result := cnt;
}

// </vc-code>
