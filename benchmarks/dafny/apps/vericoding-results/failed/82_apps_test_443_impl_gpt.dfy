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
// no changes needed
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
    var j := 1;
    var m := 0;
    while j < n
      invariant 1 <= j <= n
      invariant 0 <= m < j
      invariant forall i :: 0 <= i < j ==> packets[m] <= packets[i]
      invariant forall k :: 0 <= k < m ==> packets[k] > packets[m]
      decreases n - j
    {
      if packets[j] < packets[m] {
        m := j;
      }
      j := j + 1;
    }
    result := [1, m + 1];
    assert |packets| == n;
    assert 0 <= m < |packets|;
    assert result[1] == m + 1;
    assert forall i :: 0 <= i < |packets| ==> packets[m] <= packets[i];
    assert forall k :: 0 <= k < m ==> packets[k] > packets[m];
    assert exists minIndex ::
      0 <= minIndex < |packets| &&
      result[1] == minIndex + 1 &&
      (forall i :: 0 <= i < |packets| ==> packets[minIndex] <= packets[i]) &&
      (forall k :: 0 <= k < minIndex ==> packets[k] > packets[minIndex]);
  }
}
// </vc-code>

