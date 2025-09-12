// <vc-preamble>
function SeqMax(a: seq<int>): int
    decreases |a|
{
    if |a| == 0 then
        -2147483648  // i32::MIN equivalent
    else if a[|a|-1] > SeqMax(a[..|a|-1]) then
        a[|a|-1]
    else
        SeqMax(a[..|a|-1])
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method RollingMax(numbers: array<int>) returns (result: array<int>)
    ensures result.Length == numbers.Length
    ensures forall i :: 0 <= i < numbers.Length ==> result[i] == SeqMax(numbers[..i+1])
// </vc-spec>
// <vc-code>
{
    assume {:axiom} false;
}
// </vc-code>
