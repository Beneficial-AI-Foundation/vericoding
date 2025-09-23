// <vc-preamble>
predicate ValidInput(armies: seq<int>, k: int)
{
    |armies| >= 2 && k >= 1 && 
    forall i :: 0 <= i < |armies| ==> 1 <= armies[i] < 0x100000000
}

function countBits(x: bv32): int
{
    if x == 0 then 0
    else (if (x & 1) == 1 then 1 else 0) + countBits(x >> 1)
}

function CanBeFriends(army1: int, army2: int, k: int): bool
    requires 1 <= army1 < 0x100000000
    requires 1 <= army2 < 0x100000000
    requires k >= 1
{
    countBits((army1 as bv32) ^ (army2 as bv32)) <= k
}

function CountFriends(armies: seq<int>, k: int): int
    requires ValidInput(armies, k)
{
    |set i | 0 <= i < |armies| - 1 && countBits((armies[i] as bv32) ^ (armies[|armies|-1] as bv32)) <= k|
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method solve(armies: seq<int>, k: int) returns (result: int)
    requires ValidInput(armies, k)
    ensures result >= 0
    ensures result <= |armies| - 1
    ensures result == CountFriends(armies, k)
// </vc-spec>
// <vc-code>
{
    result := 0;
    var fedorArmy := armies[|armies| - 1] as bv32;
    var i := 0;

    while i < |armies| - 1
        invariant 0 <= i <= |armies| - 1
        invariant result >= 0
        invariant result <= i
        invariant result == |set j | 0 <= j < i && countBits((armies[j] as bv32) ^ fedorArmy) <= k|
        invariant fedorArmy == armies[|armies| - 1] as bv32
    {
        var playerArmy := armies[i] as bv32;
        var xorResult := playerArmy ^ fedorArmy;
        var bitCount := 0;
        var temp := xorResult;

        while temp != 0
            invariant bitCount >= 0
            invariant bitCount + countBits(temp) == countBits(xorResult)
        {
            if (temp & 1) == 1 {
                bitCount := bitCount + 1;
            }
            temp := temp >> 1;
        }

        assert bitCount == countBits(xorResult);
        assert xorResult == (armies[i] as bv32) ^ fedorArmy;
        assert bitCount == countBits((armies[i] as bv32) ^ fedorArmy);

        var oldSet := set j | 0 <= j < i && countBits((armies[j] as bv32) ^ fedorArmy) <= k;
        var newSet := set j | 0 <= j < i + 1 && countBits((armies[j] as bv32) ^ fedorArmy) <= k;

        if bitCount <= k {
            assert i in newSet;
            assert i !in oldSet;
            assert newSet == oldSet + {i};
            assert |newSet| == |oldSet| + 1;
            result := result + 1;
        } else {
            assert i !in newSet;
            assert newSet == oldSet;
            assert |newSet| == |oldSet|;
        }

        i := i + 1;
    }

    assert result == |set j | 0 <= j < |armies| - 1 && countBits((armies[j] as bv32) ^ fedorArmy) <= k|;
    assert fedorArmy == armies[|armies| - 1] as bv32;
    assert result == |set j | 0 <= j < |armies| - 1 && countBits((armies[j] as bv32) ^ (armies[|armies| - 1] as bv32)) <= k|;
}
// </vc-code>
