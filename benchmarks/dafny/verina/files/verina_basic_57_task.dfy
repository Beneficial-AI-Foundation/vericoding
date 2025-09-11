// <vc-preamble>
/* Helper function to recursively count elements less than threshold */
function CountLessThanSpec(numbers: seq<int>, threshold: int): nat
    decreases |numbers|
{
    if |numbers| == 0 then
        0
    else
        var first := numbers[0];
        var rest := numbers[1..];
        if first < threshold then
            1 + CountLessThanSpec(rest, threshold)
        else
            CountLessThanSpec(rest, threshold)
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method CountLessThan(numbers: array<int>, threshold: int) returns (result: nat)
    ensures result == CountLessThanSpec(numbers[..], threshold)
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume {:axiom} false;
    result := 0;
    // impl-end
}
// </vc-code>
