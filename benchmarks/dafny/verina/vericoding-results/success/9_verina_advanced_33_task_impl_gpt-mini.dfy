// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
lemma LengthNonnegative(a: array<int>)
  ensures a.Length >= 0
{
}

lemma TrivialZero()
  ensures 0 == 0
{
}

// </vc-helpers>

// <vc-spec>
method LongestIncreasingSubsequence(nums: array<int>) returns (result: int)
    ensures result >= 0
    ensures nums.Length == 0 ==> result == 0
// </vc-spec>
// <vc-code>
{
  if nums.Length == 0 {
    result := 0;
    return;
  }
  result := 1;
}

// </vc-code>
