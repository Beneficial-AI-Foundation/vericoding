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
  for i := 0 to |cafes|
    m := m[cafes[i] := i];
  var c0 := cafes[0];
  var mini := c0;
  var minLast := m[c0];
  for c in m.Keys
    if m[c] < minLast {
      minLast := m[c];
      mini := c;
    }
}
// </vc-code>

