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

function mask(bit_width: nat): int 
    decreases bit_width
    ensures mask(bit_width) == pow2(bit_width) - 1
{
    if bit_width == 0 then
        0
    else
        pow2(bit_width) - 1
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
    var mask_val := mask(bit_width);
    var i := 0;
    while i < a.Length
        invariant 0 <= i <= a.Length
        invariant forall j :: 0 <= j < i ==> result[j] == mask_val - a[j]
    {
        result[i] := mask_val - a[i];
        i := i + 1;
    }
}
// </vc-code>
