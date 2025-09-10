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
    return;
  }
  var minIdx := 0;
  var i := 1;
  while i < n
    invariant 0 <= i <= n
    invariant 0 <= minIdx < n
    invariant minIdx < i
    invariant forall j :: 0 <= j < i ==> packets[minIdx] <= packets[j]
    invariant forall k :: 0 <= k < minIdx ==> packets[k] > packets[minIdx]
  {
    if packets[i] < packets[minIdx] {
      minIdx := i;
    }
    i := i + 1;
  }
  result := [1, minIdx + 1];
}
// </vc-code>

