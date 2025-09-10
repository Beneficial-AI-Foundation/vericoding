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
// No updates needed in helpers for this fix
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
    var minVal := packets[0];
    var minIndex := 0;
    var i := 1;
    while i < n
      invariant 1 <= i <= n
      invariant 0 <= minIndex < n
      invariant minVal == packets[minIndex]
      invariant forall k :: 0 <= k < minIndex ==> minVal < packets[k]
      invariant forall j :: 0 <= j < i ==> minVal <= packets[j]
    {
      if packets[i] < minVal {
        minVal := packets[i];
        minIndex := i;
      }
      i := i + 1;
    }
    result := [1, minIndex + 1];
  }
}
// </vc-code>

