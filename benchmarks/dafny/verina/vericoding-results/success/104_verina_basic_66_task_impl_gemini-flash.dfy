// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function IsEven(x: int): bool {
    if x % 2 == 0 then true else false
}
// </vc-helpers>

// <vc-spec>
method ComputeIsEven(x: int) returns (result: bool)
    ensures result == true <==> x % 2 == 0
// </vc-spec>
// <vc-code>
{
    result := IsEven(x);
}
// </vc-code>
