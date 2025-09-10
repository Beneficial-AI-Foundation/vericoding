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
// </vc-helpers>

// <vc-spec>
method solve(n: int, packets: seq<int>) returns (result: seq<int>)
    requires ValidInput(n, packets)
    ensures ValidSolution(n, packets, result)
// </vc-spec>
// <vc-code>
if !IsPossible(n, packets) {
  result := [];
} else {
  var minIndex := 0;
  for i := 1 to n-1
    invariant 0 <= minIndex < n
    invariant forall j :: 0 <= j < i ==> packets[minIndex] <= packets[j]
    invariant 0 <= minIndex && (forall k :: 0 <= k < minIndex ==> packets[k] > packets[minIndex])
  {
    if packets[i] < packets[minIndex] {
      minIndex := i;
    }
  }
  // We need to ensure result[1] in range, which it is since minIndex between 0 and n-1
  ghost var minVal := packets[minIndex];
  // Ensuring minVal is indeed the minimum and minIndex is the first occurrence
  calc {
    forall j :: 0 <= j < n ==> minVal <= packets[j];
    {
      forall j :: 0 <= j <= minIndex-1 ==> minVal <= packets[j]; // because packets[j] > minVal from invariant
      minVal <= packets[minIndex];
      forall j :: minIndex+1 <= j < n ==> minVal <= packets[j]; // from invariant, since if j > minIndex, it's in the loop after setting
    }
  }
  result := [1, minIndex + 1];
}
// </vc-code>

