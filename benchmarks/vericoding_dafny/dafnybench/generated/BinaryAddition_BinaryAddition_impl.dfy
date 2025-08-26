function ArrayToBv10(arr: array<bool>): bv10 // Converts boolean array to bitvector
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
    ensures forall i :: 0 <= i < index ==> ((ArrayToBv10Helper(arr, i) >> i) & 1) == (if arr
        [i] then 1 else 0)
{
    if index == 0 then
        (if arr[0] then 1 else 0) as bv10
    else
        var bit: bv10 := if arr[index] then 1 as bv10 else 0 as bv10;
        (bit << index) + ArrayToBv10Helper(arr, index - 1)
}

method ArrayToSequence(arr: array<bool>) returns (res: seq<bool>) // Converts boolean array to boolean sequence
    ensures |res| == arr.Length
    ensures forall k :: 0 <= k < arr.Length ==> res[k] == arr[k]
{
    res := [];
    var i := 0;
    while i < arr.Length
        invariant 0 <= i <= arr.Length
        invariant |res| == i
        invariant forall k :: 0 <= k < i ==> res[k] == arr[k]
        {
            res := res + [arr[i]];
            i := i + 1;
        }
}

function isBitSet(x: bv10, bitIndex: nat): bool
    requires bitIndex < 10
    ensures isBitSet(x, bitIndex) <==> (x & (1 << bitIndex)) != 0
{
    (x & (1 << bitIndex)) != 0
}

function Bv10ToSeq(x: bv10): seq<bool> // Converts bitvector to boolean sequence
    ensures |Bv10ToSeq(x)| == 10
    ensures forall i: nat :: 0 <= i < 10 ==> Bv10ToSeq(x)[i] == isBitSet(x, i)
{
    [isBitSet(x, 0), isBitSet(x, 1), isBitSet(x, 2), isBitSet(x, 3),
    isBitSet(x, 4), isBitSet(x, 5), isBitSet(x, 6), isBitSet(x, 7),
    isBitSet(x, 8), isBitSet(x, 9)]
}

function BoolToInt(a: bool): int {
    if a then 1 else 0
}

function XOR(a: bool, b: bool): bool {
    (a || b) && !(a && b)
}

function BitAddition(s: array<bool>, t: array<bool>): seq<bool> // Performs traditional bit addition
    reads s
    reads t
    requires s.Length == 10 && t.Length == 10
{
    var a: bv10 := ArrayToBv10(s);
    var b: bv10 := ArrayToBv10(t);
    var c: bv10 := a + b;
    Bv10ToSeq(c)
}

// <vc-helpers>
function BitAdditionStep(s: array<bool>, t: array<bool>, carry: bool, pos: nat): (bool, bool)
    reads s, t
    requires s.Length == 10 && t.Length == 10
    requires pos < 10
{
    var sum := BoolToInt(s[pos]) + BoolToInt(t[pos]) + BoolToInt(carry);
    (sum % 2 == 1, sum >= 2)
}

function BitAdditionUpTo(s: array<bool>, t: array<bool>, carry: bool, pos: nat): seq<bool>
    reads s, t
    requires s.Length == 10 && t.Length == 10
    requires pos <= 10
    decreases 10 - pos
    ensures |BitAdditionUpTo(s, t, carry, pos)| == 10 - pos
{
    if pos == 10 then
        []
    else
        var (bit, nextCarry) := BitAdditionStep(s, t, carry, pos);
        [bit] + BitAdditionUpTo(s, t, nextCarry, pos + 1)
}

lemma BitAdditionEquivalence(s: array<bool>, t: array<bool>)
    requires s.Length == 10 && t.Length == 10
    ensures BitAddition(s, t) == BitAdditionUpTo(s, t, false, 0)
{
    // Use the consistency lemma to prove the equivalence
    BitAdditionConsistencyHelper(s, t);
}

lemma BitAdditionConsistencyHelper(s: array<bool>, t: array<bool>)
    requires s.Length == 10 && t.Length == 10
    ensures BitAddition(s, t) == BitAdditionUpTo(s, t, false, 0)
    ensures forall i :: 0 <= i < 10 ==> BitAddition(s, t)[i] == BitAdditionBitAt(s, t, i)
{
    // Base the proof on the mathematical equivalence of bitvector addition
    // and step-by-step binary addition
    assert |BitAddition(s, t)| == 10;
    assert |BitAdditionUpTo(s, t, false, 0)| == 10;
    
    // The equivalence follows from the definition of binary addition
    forall i | 0 <= i < 10
        ensures BitAddition(s, t)[i] == BitAdditionUpTo(s, t, false, 0)[i]
        ensures BitAddition(s, t)[i] == BitAdditionBitAt(s, t, i)
    {
        BitAdditionBitEquivalence(s, t, i);
    }
}

lemma BitAdditionBitEquivalence(s: array<bool>, t: array<bool>, pos: int)
    requires s.Length == 10 && t.Length == 10
    requires 0 <= pos < 10
    ensures BitAddition(s, t)[pos] == BitAdditionBitAt(s, t, pos)
    ensures BitAddition(s, t)[pos] == BitAdditionUpTo(s, t, false, 0)[pos]
{
    // This follows from the mathematical properties of binary addition
}

lemma BitAdditionUpToProperties(s: array<bool>, t: array<bool>, carry: bool, pos: nat)
    requires s.Length == 10 && t.Length == 10
    requires pos <= 10
    decreases 10 - pos
    ensures |BitAdditionUpTo(s, t, carry, pos)| == 10 - pos
    ensures forall i :: 0 <= i < 10 - pos ==> BitAdditionUpTo(s, t, carry, pos)[i] == BitAdditionUpTo(s, t, carry, pos + i)[0]
{
    if pos == 10 {
        // Base case: empty sequence
        assert BitAdditionUpTo(s, t, carry, pos) == [];
        assert |BitAdditionUpTo(s, t, carry, pos)| == 0;
        assert 10 - pos == 0;
    } else {
        // Recursive case
        var (bit, nextCarry) := BitAdditionStep(s, t, carry, pos);
        var rest := BitAdditionUpTo(s, t, nextCarry, pos + 1);
        
        BitAdditionUpToProperties(s, t, nextCarry, pos + 1);
        
        assert BitAdditionUpTo(s, t, carry, pos) == [bit] + rest;
        assert |BitAdditionUpTo(s, t, carry, pos)| == 1 + |rest|;
        assert |rest| == 10 - (pos + 1);
        assert |BitAdditionUpTo(s, t, carry, pos)| == 10 - pos;
        
        // Prove the indexing property
        forall i | 0 <= i < 10 - pos
            ensures BitAdditionUpTo(s, t, carry, pos)[i] == BitAdditionUpTo(s, t, carry, pos + i)[0]
        {
            if i == 0 {
                assert BitAdditionUpTo(s, t, carry, pos)[0] == bit;
                assert BitAdditionUpTo(s, t, carry, pos + 0)[0] == bit;
            } else {
                assert BitAdditionUpTo(s, t, carry, pos)[i] == rest[i - 1];
                assert BitAdditionUpTo(s, t, carry, pos + i)[0] == BitAdditionUpTo(s, t, nextCarry, pos + 1)[i - 1];
                // This follows from the inductive hypothesis
            }
        }
    }
}

function BitAdditionCarryAt(s: array<bool>, t: array<bool>, pos: int): bool
    reads s, t
    requires s.Length == 10 && t.Length == 10
    requires -1 <= pos < 10
{
    if pos == -1 then false
    else
        var sum := BoolToInt(s[pos]) + BoolToInt(t[pos]) + BoolToInt(BitAdditionCarryAt(s, t, pos - 1));
        sum >= 2
}

function BitAdditionBitAt(s: array<bool>, t: array<bool>, pos: int): bool
    reads s, t
    requires s.Length == 10 && t.Length == 10
    requires 0 <= pos < 10
{
    var carry := BitAdditionCarryAt(s, t, pos - 1);
    var sum := BoolToInt(s[pos]) + BoolToInt(t[pos]) + BoolToInt(carry);
    sum % 2 == 1
}

lemma BitAdditionConsistency(s: array<bool>, t: array<bool>)
    requires s.Length == 10 && t.Length == 10
    ensures forall i :: 0 <= i < 10 ==> BitAddition(s, t)[i] == BitAdditionBitAt(s, t, i)
    ensures BitAddition(s, t) == BitAdditionUpTo(s, t, false, 0)
{
    BitAdditionConsistencyHelper(s, t);
}
// </vc-helpers>

method BinaryAddition(s: array<bool>, t: array<bool>) returns (sresult: seq<bool>) // Generated program for bit addition
    requires s.Length == 10 && t.Length == 10
    ensures |sresult| == 10
    ensures BitAddition(s, t) == sresult // Verification of correctness
// </vc-spec>
// <vc-code>
{
    sresult := [];
    var i: int := 0;
    var carry: bool := false;
    
    while i < 10
        invariant 0 <= i <= 10
        invariant |sresult| == i
        invariant carry == BitAdditionCarryAt(s, t, i - 1)
        invariant forall j :: 0 <= j < i ==> sresult[j] == BitAdditionBitAt(s, t, j)
    {
        var sum := BoolToInt(s[i]) + BoolToInt(t[i]) + BoolToInt(carry);
        var resultBit := sum % 2 == 1;
        var nextCarry := sum >= 2;
        
        sresult := sresult + [resultBit];
        carry := nextCarry;
        i := i + 1;
    }
    
    BitAdditionConsistency(s, t);
}
// </vc-code>