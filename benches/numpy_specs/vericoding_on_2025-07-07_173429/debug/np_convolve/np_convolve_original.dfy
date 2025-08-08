//SPEC
function convolve(arr1: seq<real>, arr2: seq<real>): seq<real>
    requires |arr1| > 0 && |arr2| > 0
    ensures |convolve(arr1, arr2)| == |arr1| + |arr2| - 1
{
    seq(|arr1| + |arr2| - 1, n => ConvolutionSum(arr1, arr2, n))
}

// Helper function to express the convolution sum mathematically
function ConvolutionSum(arr1: seq<real>, arr2: seq<real>, n: int): real
    requires |arr1| > 0 && |arr2| > 0
    requires 0 <= n < |arr1| + |arr2| - 1
{
    sum i | 0 <= i < |arr1| && 0 <= n - i < |arr2| :: arr1[i] * arr2[n - i]
}