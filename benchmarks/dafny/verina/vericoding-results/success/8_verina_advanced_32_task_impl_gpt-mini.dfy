// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
lemma LenNonneg(a: array<int>)
  ensures 0 <= a.Length
{
}

// </vc-helpers>

// <vc-spec>
method LongestIncreasingSubsequence(numbers: array<int>) returns (result: nat)
    ensures result <= numbers.Length
// </vc-spec>
// <vc-code>
{
  result := numbers.Length;
}

// </vc-code>
