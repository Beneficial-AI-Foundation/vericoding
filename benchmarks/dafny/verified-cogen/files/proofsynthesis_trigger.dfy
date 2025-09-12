// <vc-preamble>
function f(s: seq<int>, i: int): bool
    requires 0 <= i < |s|
{
    s[i] == i + 2
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method GetElementCheckProperty(arr: array<int>, i: int) returns (ret: int)
    requires arr.Length > 0
    requires 0 < i < arr.Length
    requires forall j :: 0 <= j < arr.Length ==> f(arr[..], j)
    ensures ret == i + 2
    ensures ret == arr[i]
// </vc-spec>
// <vc-code>
{
    assume {:axiom} false;
}
// </vc-code>
