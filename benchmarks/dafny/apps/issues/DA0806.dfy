// <vc-preamble>
predicate ValidInput(n: int, s: seq<int>)
{
    n >= 1 && |s| == n && forall i :: 0 <= i < |s| ==> 0 <= s[i] < 0x40000000
}

function BitwiseXor(a: int, b: int): int
    requires a >= 0 && b >= 0
    requires a < 0x100000000 && b < 0x100000000
{
    BitvectorToInt((a as bv32) ^ (b as bv32))
}

function BitvectorToInt(bv: bv32): int
{
    bv as int
}

function MaxXorValue(s: seq<int>, X: int): int
    requires forall i :: 0 <= i < |s| ==> s[i] >= 0
    requires X >= 0
    requires forall i :: 0 <= i < |s| ==> s[i] < 0x100000000
    requires X < 0x100000000
    ensures MaxXorValue(s, X) >= 0
    ensures |s| > 0 ==> MaxXorValue(s, X) < 0x100000000
{
    if |s| == 0 then 0
    else
        var xor_values := seq(|s|, i requires 0 <= i < |s| => BitwiseXor(s[i], X));
        Max(xor_values)
}

function Max(s: seq<int>): int
    requires |s| > 0
    requires forall i :: 0 <= i < |s| ==> s[i] >= 0
    ensures Max(s) >= 0
    ensures forall i :: 0 <= i < |s| ==> Max(s) >= s[i]
    ensures exists i :: 0 <= i < |s| && Max(s) == s[i]
{
    if |s| == 1 then s[0]
    else if s[0] >= Max(s[1..]) then s[0]
    else Max(s[1..])
}

predicate IsMinimumMaxXor(s: seq<int>, result: int)
    requires forall i :: 0 <= i < |s| ==> 0 <= s[i] < 0x40000000
{
    result >= 0 &&
    result < 0x40000000 &&
    exists X :: 0 <= X < 0x40000000 && result == MaxXorValue(s, X) &&
    forall X :: 0 <= X < 0x40000000 ==> result <= MaxXorValue(s, X)
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method solve(n: int, s: seq<int>) returns (result: int)
    requires ValidInput(n, s)
    ensures IsMinimumMaxXor(s, result)
// </vc-spec>
// <vc-code>
{
    result := MaxXorValue(s, 0);
    var X := 1;

    while X < 0x40000000
        invariant 1 <= X <= 0x40000000
        invariant result >= 0
        invariant result < 0x40000000
        invariant exists Y :: 0 <= Y < X && result == MaxXorValue(s, Y)
        invariant forall Y :: 0 <= Y < X ==> result <= MaxXorValue(s, Y)
    {
        var currentMax := MaxXorValue(s, X);
        if currentMax < result {
            result := currentMax;
        }
        X := X + 1;
    }
}
// </vc-code>
