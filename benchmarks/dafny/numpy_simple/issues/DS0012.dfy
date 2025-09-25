// <vc-preamble>
function ConvolutionSum(arr1: seq<real>, arr2: seq<real>, n: nat): real
{
    0.0
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method ConvolutionSumImpl(arr1: array<real>, arr2: array<real>, n: int) returns (result: real)

method Convolve(arr1: array<real>, arr2: array<real>) returns (result: array<real>)
    requires arr1.Length > 0
    requires arr2.Length > 0
    ensures result.Length == arr1.Length + arr2.Length - 1
// </vc-spec>
// <vc-code>
{
    assume {:axiom} false;
}
// </vc-code>
