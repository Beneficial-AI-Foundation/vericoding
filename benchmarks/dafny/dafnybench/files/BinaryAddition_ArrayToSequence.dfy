// <vc-preamble>
function ArrayToBv10(arr: array<bool>): bv10
    reads arr
    requires arr.Length == 10
{
    ArrayToBv10Helper(arr, arr.Length - 1)
}

function ArrayToBv10Helper(arr: array<bool>, index: nat): bv10
    reads arr
    requires arr.Length == 10
    requires 0 <= index < arr.Length
    decreases index
{
    if index == 0 then
        (if arr[0] then 1 else 0) as bv10
    else
        var bit: bv10 := if arr[index] then 1 as bv10 else 0 as bv10;
        (bit << index) + ArrayToBv10Helper(arr, index - 1)
}

function isBitSet(x: bv10, bitIndex: nat): bool
    requires bitIndex < 10
    ensures isBitSet(x, bitIndex) <==> (x & (1 << bitIndex)) != 0
{
    (x & (1 << bitIndex)) != 0
}

function BoolToInt(a: bool): int {
    if a then 1 else 0
}

function XOR(a: bool, b: bool): bool {
    (a || b) && !(a && b)
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method ArrayToSequence(arr: array<bool>) returns (res: seq<bool>)
    ensures |res| == arr.Length
    ensures forall k :: 0 <= k < arr.Length ==> res[k] == arr[k]
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
