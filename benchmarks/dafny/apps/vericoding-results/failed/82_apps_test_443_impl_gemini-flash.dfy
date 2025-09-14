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
function min_index(packets: seq<int>): int
    requires |packets| > 0
    ensures 0 <= min_index(packets) < |packets|
    ensures forall j :: 0 <= j < |packets| ==> packets[min_index(packets)] <= packets[j]
    ensures forall k :: 0 <= k < min_index(packets) ==> packets[k] > packets[min_index(packets)]
{
    if |packets| == 1 then
        0
    else
        var rest_min_idx := min_index(packets[1..]);
        if packets[0] <= packets[rest_min_idx + 1] then
            0
        else
            rest_min_idx + 1
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, packets: seq<int>) returns (result: seq<int>)
    requires ValidInput(n, packets)
    ensures ValidSolution(n, packets, result)
// </vc-spec>
// <vc-code>
{
    if !IsPossible(n, packets) then
        result := [];
    else
        var minIdx := min_index(packets);
        result := [1, minIdx + 1];
    return result;
}
// </vc-code>

