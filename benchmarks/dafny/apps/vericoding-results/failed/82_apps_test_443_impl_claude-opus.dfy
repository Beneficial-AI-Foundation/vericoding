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
    requires |packets| >= 1
    requires forall i :: 0 <= i < |packets| ==> packets[i] >= 1
    ensures exists minIndex :: (0 <= minIndex < |packets| && 
            (forall j :: 0 <= j < |packets| ==> packets[minIndex] <= packets[j]) &&
            (forall k :: 0 <= k < minIndex ==> packets[k] > packets[minIndex]))
{
    var minVal := packets[0];
    var minIdx := 0;
    var i := 1;
    
    while i < |packets|
        invariant 0 <= i <= |packets|
        invariant 0 <= minIdx < i
        invariant minVal == packets[minIdx]
        invariant forall j :: 0 <= j < i ==> packets[minIdx] <= packets[j]
        invariant forall k :: 0 <= k < minIdx ==> packets[k] > packets[minIdx]
    {
        if packets[i] < minVal {
            minVal := packets[i];
            minIdx := i;
        }
        i := i + 1;
    }
    
    assert minIdx >= 0 && minIdx < |packets|;
    assert forall j :: 0 <= j < |packets| ==> packets[minIdx] <= packets[j];
    assert forall k :: 0 <= k < minIdx ==> packets[k] > packets[minIdx];
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, packets: seq<int>) returns (result: seq<int>)
    requires ValidInput(n, packets)
    ensures ValidSolution(n, packets, result)
// </vc-spec>
// <vc-code>
{
    if n < 2 {
        result := [];
        return;
    }
    
    if n == 2 && packets[0] == packets[1] {
        result := [];
        return;
    }
    
    // Find the index of the minimum element (first occurrence)
    var minVal := packets[0];
    var minIndex := 0;
    var i := 1;
    
    while i < n
        invariant 0 <= i <= n
        invariant 0 <= minIndex < i
        invariant minVal == packets[minIndex]
        invariant forall j :: 0 <= j < i ==> packets[minIndex] <= packets[j]
        invariant forall k :: 0 <= k < minIndex ==> packets[k] > packets[minIndex]
    {
        if packets[i] < minVal {
            minVal := packets[i];
            minIndex := i;
        }
        i := i + 1;
    }
    
    result := [1, minIndex + 1];
    
    // Establish the existential witness
    assert minIndex >= 0 && minIndex < |packets|;
    assert result[1] == minIndex + 1;
    assert forall j :: 0 <= j < |packets| ==> packets[minIndex] <= packets[j];
    assert forall k :: 0 <= k < minIndex ==> packets[k] > packets[minIndex];
}
// </vc-code>

