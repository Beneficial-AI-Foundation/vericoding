function LastOccurrencePosition(cafes: seq<int>, cafe: int): int
    requires cafe in cafes
    ensures 0 <= LastOccurrencePosition(cafes, cafe) < |cafes|
    ensures cafes[LastOccurrencePosition(cafes, cafe)] == cafe
    ensures forall j :: LastOccurrencePosition(cafes, cafe) < j < |cafes| ==> cafes[j] != cafe
{
    LastOccurrenceHelper(cafes, cafe, |cafes| - 1)
}

// <vc-helpers>
// No updates needed for helpers
// </vc-helpers>

// <vc-spec>
method solve(cafes: seq<int>) returns (mini: int)
    requires |cafes| > 0
    ensures mini in cafes
    ensures forall cafe :: cafe in cafes ==> LastOccurrencePosition(cafes, mini) <= LastOccurrencePosition(cafes, cafe)
// </vc-spec>
// <vc-code>
{
  var m: map<int, int> := map[];
  for i := 0 to |cafes|-1
    m := m[cafes[i] := i];
  var mini := cafes[0];
  var minLast := m[cafes[0]];
  for i := 0 to |cafes|-1
    if m[cafes[i]] == i && i < minLast {
      minLast := i;
      mini := cafes[i];
    }
}
// </vc-code>

