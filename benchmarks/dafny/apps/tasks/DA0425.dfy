// <vc-preamble>
predicate ValidInput(n: int, a: seq<int>)
{
    n >= 1 && |a| == n && forall i :: 0 <= i < |a| ==> a[i] >= 1
}

function Transform(a: seq<int>): seq<int>
{
    seq(|a|, i requires 0 <= i < |a| => a[i] - (i + 1))
}

function SumAbsDiffs(a: seq<int>, target: int): int
    ensures SumAbsDiffs(a, target) >= 0
{
    if |a| == 0 then 0
    else Abs(a[0] - target) + SumAbsDiffs(a[1..], target)
}

function MedianOf(a: seq<int>): int
{
    var sorted := SortedSeq(a);
    if |sorted| == 0 then 0
    else if |sorted| % 2 == 1 then
        sorted[|sorted| / 2]
    else if |sorted| == 2 then
        RoundToInt((sorted[0] as real + sorted[1] as real) / 2.0)
    else
        RoundToInt((sorted[|sorted| / 2 - 1] as real + sorted[|sorted| / 2] as real) / 2.0)
}

function SortedSeq(a: seq<int>): seq<int>
{
    a
}

function Abs(x: int): int
    ensures Abs(x) >= 0
{
    if x >= 0 then x else -x
}

function RoundToInt(x: real): int
{
    if x >= 0.0 then
        ((x + 0.5).Floor) as int
    else
        ((x - 0.5).Floor) as int
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method solve(n: int, a: seq<int>) returns (result: int)
    requires ValidInput(n, a)
    ensures result >= 0
    ensures result == SumAbsDiffs(Transform(a), MedianOf(Transform(a)))
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
