predicate ValidInput(n: int, packets: seq<int>)
{
    n >= 1 && |packets| == n && forall i :: 0 <= i < |packets| ==> packets[i] >= 1
}

predicate IsPossible(n: int, packets: seq<int>)
    requires ValidInput(n, packets)
{
    n >= 2 && (n > 2 || packets[0] != packets[1])
}

function SumPackets(packets: seq<int>): int
{
    if |packets| == 0 then 0 else packets[0] + SumPackets(packets[1..])
}

predicate ValidSolution(n: int, packets: seq<int>, result: seq<int>)
    requires ValidInput(n, packets)
{
    if !IsPossible(n, packets) then
        |result| == 0
    else
        |result| == 2 && result[0] == 1 && 1 <= result[1] <= n &&
        exists minIndex :: 0 <= minIndex < |packets| && 
        result[1] == minIndex + 1 &&
        (forall j :: 0 <= j < |packets| ==> packets[minIndex] <= packets[j]) &&
        (forall k :: 0 <= k < minIndex ==> packets[k] > packets[minIndex])
}

// <vc-helpers>
function FindMinIndex(packets: seq<int>): (minIndex: int)
    requires |packets| > 0
    ensures 0 <= minIndex < |packets|
    ensures forall j :: 0 <= j < |packets| ==> packets[minIndex] <= packets[j]
    ensures forall k :: 0 <= k < minIndex ==> packets[k] > packets[minIndex]
{
    if |packets| == 1 then 0 else
        var prevMinIndex := FindMinIndex(packets[1..]);
        if prevMinIndex + 1 < |packets| && packets[prevMinIndex + 1] < packets[0] then 
            prevMinIndex + 1
        else 
            0
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, packets: seq<int>) returns (result: seq<int>)
    requires ValidInput(n, packets)
    ensures ValidSolution(n, packets, result)
// </vc-spec>
// <vc-code>
{
    if !IsPossible(n, packets) {
        result := [];
    } else {
        var minIndex := FindMinIndex(packets);
        result := [1, minIndex + 1];
    }
}
// </vc-code>

