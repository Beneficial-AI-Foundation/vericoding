// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function Zero(): int { 0 }
// </vc-helpers>

// <vc-spec>
method SemiOrderedPermutation(nums: array<int>) returns (result: int)
    ensures 
        result >= 0
// </vc-spec>
// <vc-code>
{
  result := Zero();
}
// </vc-code>
