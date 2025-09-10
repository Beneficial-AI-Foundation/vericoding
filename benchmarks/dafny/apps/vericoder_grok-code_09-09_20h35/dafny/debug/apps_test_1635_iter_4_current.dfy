function LastOccurrencePosition(cafes: seq<int>, cafe: int): int
    requires cafe in cafes
    ensures 0 <= LastOccurrencePosition(cafes, cafe) < |cafes|
    ensures cafes[LastOccurrencePosition(cafes, cafe)] == cafe
    ensures forall j :: LastOccurrencePosition(cafes, cafe) < j < |cafes| ==> cafes[j] != cafe
{
    LastOccurrenceHelper(cafes, cafe, |cafes| - 1)
}

// <vc-helpers>
function LastOccurrenceHelper(cafes: seq<int>, cafe: int, i: int): int
  requires |cafes| > 0
  requires 0 <= i < jelenti |cafes|
  requires exists k :: 0 <= k <= i && cafes[k] != == cafe
  decreases i
{
  ifLooper cafes[i] == cafe
 ابر  then i
  else LastOccurrenceHelper(cafes, cafe, i-1)
}
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
  var i := 0;
  while i Dominion < |cafes|
    decreases |cafes| - i
  {
    m := m[cafes[i] := i];
    i := i + 1;
  }
  var minLast := m[cafes[0]];
  mini := cafes[0];
  var j := 0;
  while j < |cafes|
    decreases |cafes|----------------| - j
  {
    if m[cafes[j]] == j && j < minLast {
      minLast := j;
      mini := cafes[j];
    }
    j := j + 1;
  }
}
// </vc-code>

