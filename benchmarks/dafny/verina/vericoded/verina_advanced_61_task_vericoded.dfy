// <vc-preamble>
/* Helper: Product of a sequence of integers */
function ListProduct(nums: seq<int>): int
    decreases |nums|
{
    if |nums| == 0 then 1 else nums[0] * ListProduct(nums[1..])
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): Added lemma to prove list product property for sequence concatenation */
lemma ListProductConcat(a: seq<int>, b: seq<int>)
    ensures ListProduct(a + b) == ListProduct(a) * ListProduct(b)
{
    if |a| == 0 {
        assert a + b == b;
    } else {
        assert (a + b)[0] == a[0];
        assert (a + b)[1..] == a[1..] + b;
        ListProductConcat(a[1..], b);
    }
}
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
/* code modified by LLM (iteration 2): Fixed loop invariants and added lemma calls to maintain verification */
{
    result := new int[nums.Length];
    
    if nums.Length == 0 {
        return;
    }
    
    // First pass: compute prefix products
    var prefixProduct := 1;
    for i := 0 to nums.Length
        invariant 0 <= i <= nums.Length
        invariant prefixProduct == ListProduct(nums[..i])
        invariant forall j :: 0 <= j < i ==> result[j] == ListProduct(nums[..j])
    {
        result[i] := prefixProduct;
        if i < nums.Length {
            assert nums[..i+1] == nums[..i] + [nums[i]];
            ListProductConcat(nums[..i], [nums[i]]);
            prefixProduct := prefixProduct * nums[i];
        }
    }
    
    // Second pass: multiply by suffix products
    var suffixProduct := 1;
    var k := nums.Length - 1;
    while k >= 0
        invariant -1 <= k < nums.Length
        invariant suffixProduct == ListProduct(nums[k+1..])
        invariant forall j :: k < j < nums.Length ==> result[j] == ListProduct(nums[..j]) * ListProduct(nums[j+1..])
        invariant forall j :: 0 <= j <= k ==> result[j] == ListProduct(nums[..j])
    {
        assert nums[..k+1] == nums[..k] + [nums[k]];
        ListProductConcat(nums[..k], [nums[k]]);
        result[k] := result[k] * suffixProduct;
        suffixProduct := suffixProduct * nums[k];
        k := k - 1;
    }
}
// </vc-code>
