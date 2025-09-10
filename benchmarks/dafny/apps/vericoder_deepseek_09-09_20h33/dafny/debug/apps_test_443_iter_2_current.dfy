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
    requires |packets| > 0
    ensures exists i :: 0 <= i < |packets| && (forall j :: 0 <= j < |packets| ==> packets[i] <= packets[j])
{
    if |packets| == 1 {
        // Only one element, so it's automatically the minimum
    } else {
        var sub := packets[1..];
        MinIndexExists(sub);
    }
}

lemma FirstMinIndexExists(packets: seq<int>)
    requires |packets| > 0
    ensures exists i :: 0 <= i < |packets| && 
        (forall j :: 0 <= j < |packets| ==> packets[i] <= packets[j]) &&
        (forall k :: 0 <= k < i ==> packets[k] > packets[i])
{
    var i := 0;
    var min_val := packets[0];
    var min_index := 0;
    
    while i < |packets|
        invariant 0 <= i <= |packets|
        invariant 0 <= min_index < |packets|
        invariant min_index < i || i == 0
        invariant min_val == packets[min_index]
        invariant forall j :: 0 <= j < i ==> min_val <= packets[j]
        invariant forall k :: 0 <= k < min_index ==> packets[k] > min_val
    {
        if packets[i] < min_val {
            min_val := packets[i];
            min_index := i;
        } else if packets[i] == min_val {
            // Keep the first occurrence
        }
        i := i + 1;
    }
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
        var min_val := packets[0];
        var min_index := 0;
        var i := 1;
        
        while i < n
            invariant 1 <= i <= n
            invariant 0 <= min_index < n
            invariant min_index < i
            invariant min_val == packets[min_index]
            invariant forall j :: 0 <= j < i ==> min_val <= packets[j]
            invariant forall k :: 0 <= k < min_index ==> packets[k] > min_val
        {
            if packets[i] < min_val {
                min_val := packets[i];
                min_index := i;
            }
            i := i + 1;
        }
        
        result := [1, min_index + 1];
    }
}
// </vc-code>

