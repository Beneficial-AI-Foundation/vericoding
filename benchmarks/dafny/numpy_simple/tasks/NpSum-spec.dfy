// <vc-preamble>
function SumRange(a: seq<int>, start: int, len: int): int
    decreases len
{
    if len <= 0 || start < 0 || start + len > |a| then
        0
    else if len == 0 then
        0
    else
        a[start] + SumRange(a, start + 1, len - 1)
}

function SeqSum(a: seq<int>): int
{
    SumRange(a, 0, |a|)
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method Sum(a: array<int>) returns (result: int)
    ensures result == SeqSum(a[..])
{
    assume {:axiom} false;
}

method SumArray(a: array<int>, start: int, finish: int) returns (result: int)
    requires start <= finish && finish <= a.Length
    ensures result == SumRange(a[..], start, finish - start)
// </vc-spec>
// <vc-code>
{
    assume {:axiom} false;
}
// </vc-code>
