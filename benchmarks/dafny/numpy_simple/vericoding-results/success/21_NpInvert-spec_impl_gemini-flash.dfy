// <vc-preamble>
function pow2(n: nat): nat 
    decreases n
{
    if n == 0 then
        1
    else
        2 * pow2(n - 1)
}
// </vc-preamble>

// <vc-helpers>
function pow2_minus_1(n: nat): nat
    decreases n
{
    if n == 0 then
        0
    else
        2 * pow2_minus_1(n - 1) + 1
}
// </vc-helpers>

// <vc-spec>
method invert(bit_width: nat, a: array<int>) returns (result: array<int>)
    ensures
        result.Length == a.Length &&
        forall i :: 0 <= i < a.Length ==> result[i] == (pow2(bit_width) - 1) - a[i]
// </vc-spec>
// <vc-code>
{
    result := new int[a.Length];
    var i := 0;
    while i < a.Length
        invariant 0 <= i <= a.Length
        invariant forall j :: 0 <= j < i ==> result[j] == (pow2(bit_width) - 1) - a[j]
    {
        result[i] := (pow2(bit_width) - 1) - a[i];
        i := i + 1;
    }
}
// </vc-code>
