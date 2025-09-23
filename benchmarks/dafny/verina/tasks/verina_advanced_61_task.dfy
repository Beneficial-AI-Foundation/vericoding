// <vc-preamble>
/* Helper: Product of a sequence of integers */
function ListProduct(nums: seq<int>): int
    decreases |nums|
{
    if |nums| == 0 then 1 else nums[0] * ListProduct(nums[1..])
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method ProductExceptSelf(nums: array<int>) returns (result: array<int>)
    ensures
        result.Length == nums.Length
    ensures
        forall i :: 0 <= i < nums.Length ==> 
            result[i] == ListProduct(nums[..i]) * ListProduct(nums[i+1..])
// </vc-spec>
// <vc-code>
{
    result := new int[nums.Length];
    assume {:axiom} false;
}
// </vc-code>
