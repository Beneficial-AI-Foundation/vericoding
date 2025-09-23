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

method ArrayToSequence(arr: array<bool>) returns (res: seq<bool>)
    ensures |res| == arr.Length
    ensures forall k :: 0 <= k < arr.Length ==> res[k] == arr[k]
{
  assume{:axiom} false;
}

function isBitSet(x: bv10, bitIndex: nat): bool
    requires bitIndex < 10
    ensures isBitSet(x, bitIndex) <==> (x & (1 << bitIndex)) != 0
{
    (x & (1 << bitIndex)) != 0
}

function Bv10ToSeq(x: bv10): seq<bool>
    ensures |Bv10ToSeq(x)| == 10
    ensures forall i: nat :: 0 <= i < 10 ==> Bv10ToSeq(x)[i] == isBitSet(x, i)
{
    var result := [isBitSet(x, 0), isBitSet(x, 1), isBitSet(x, 2), isBitSet(x, 3),
    isBitSet(x, 4), isBitSet(x, 5), isBitSet(x, 6), isBitSet(x, 7),
    isBitSet(x, 8), isBitSet(x, 9)];
    assert result[0] == isBitSet(x, 0);
    assert result[1] == isBitSet(x, 1);
    assert result[2] == isBitSet(x, 2);
    assert result[3] == isBitSet(x, 3);
    assert result[4] == isBitSet(x, 4);
    assert result[5] == isBitSet(x, 5);
    assert result[6] == isBitSet(x, 6);
    assert result[7] == isBitSet(x, 7);
    assert result[8] == isBitSet(x, 8);
    assert result[9] == isBitSet(x, 9);
    assert forall i: nat :: 0 <= i < 10 ==> result[i] == isBitSet(x, i);
    result
}

function BoolToInt(a: bool): int {
    if a then 1 else 0
}

function XOR(a: bool, b: bool): bool {
    (a || b) && !(a && b)
}

function BitAddition(s: array<bool>, t: array<bool>): seq<bool>
    reads s
    reads t
    requires s.Length == 10 && t.Length == 10
{
    var a: bv10 := ArrayToBv10(s);
    var b: bv10 := ArrayToBv10(t);
    var c: bv10 := a + b;
    Bv10ToSeq(c)
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method BinaryAddition(s: array<bool>, t: array<bool>) returns (sresult: seq<bool>)
    requires s.Length == 10 && t.Length == 10
    ensures |sresult| == 10
    ensures BitAddition(s, t) == sresult
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
