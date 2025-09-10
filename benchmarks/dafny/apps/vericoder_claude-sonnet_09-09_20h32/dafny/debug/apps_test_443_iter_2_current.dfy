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
lemma MinIndexExists(packets: seq<int>)
    requires |packets| >= 1 && forall i :: 0 <= i < |packets| ==> packets[i] >= 1
    ensures exists minIndex :: 0 <= minIndex < |packets| && 
            (forall j :: 0 <= j < |packets| ==> packets[minIndex] <= packets[j]) &&
            (forall k :: 0 <= k < minIndex ==> packets[k] > packets[minIndex])
{
    var minIndex := FindMinIndex(packets, 0, 0);
    assert 0 <= minIndex < |packets|;
    assert forall j :: 0 <= j < |packets| ==> packets[minIndex] <= packets[j];
    assert forall k :: 0 <= k < minIndex ==> packets[k] > packets[minIndex];
}

function FindMinIndex(packets: seq<int>, currentIndex: int, currentMinIndex: int): int
    requires |packets| >= 1
    requires 0 <= currentIndex <= |packets|
    requires 0 <= currentMinIndex < |packets|
    requires forall j :: 0 <= j < currentIndex ==> packets[currentMinIndex] <= packets[j]
    requires forall k :: 0 <= k < currentMinIndex ==> packets[k] > packets[currentMinIndex]
    ensures 0 <= FindMinIndex(packets, currentIndex, currentMinIndex) < |packets|
    ensures forall j :: 0 <= j < |packets| ==> packets[FindMinIndex(packets, currentIndex, currentMinIndex)] <= packets[j]
    ensures forall k :: 0 <= k < FindMinIndex(packets, currentIndex, currentMinIndex) ==> packets[k] > packets[FindMinIndex(packets, currentIndex, currentMinIndex)]
    decreases |packets| - currentIndex
{
    if currentIndex == |packets| then
        currentMinIndex
    else if packets[currentIndex] < packets[currentMinIndex] then
        FindMinIndex(packets, currentIndex + 1, currentIndex)
    else
        FindMinIndex(packets, currentIndex + 1, currentMinIndex)
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, packets: seq<int>) returns (result: seq<int>)
    requires ValidInput(n, packets)
    ensures ValidSolution(n, packets, result)
// </vc-spec>
// <vc-code>
{
    if n < 2 || (n == 2 && packets[0] == packets[1]) {
        result := [];
    } else {
        var minIndex := FindMinIndex(packets, 1, 0);
        MinIndexExists(packets);
        result := [1, minIndex + 1];
    }
}
// </vc-code>

