function LastOccurrencePosition(cafes: seq<int>, cafe: int): int
    requires cafe in cafes
    ensures 0 <= LastOccurrencePosition(cafes, cafe) < |cafes|
    ensures cafes[LastOccurrencePosition(cafes, cafe)] == cafe
    ensures forall j :: LastOccurrencePosition(cafes, cafe) < j < |cafes| ==> cafes[j] != cafe
{
    LastOccurrenceHelper(cafes, cafe, |cafes| - 1)
}

// <vc-helpers>
function LastOccurrenceHelper(cafes: seq<int>, cafe: int, k: int) : int
    requires cafe in cafes
    requires -1 <= k < |cafes|
    requires cafe in cafes[..k+1]
    decreases k
    ensures 0 <= LastOccurrenceHelper(cafes, cafe, k) <= k
    ensures cafes[LastOccurrenceHelper(cafes, cafe, k)] == cafe
    ensures forall j :: LastOccurrenceHelper(cafes, cafe, k) < j <= k ==> cafes[j] != cafe
{
    if k >= 0 && cafes[k] == cafe then k
    else LastOccurrenceHelper(cafes, cafe, k - 1)
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
  mini := cafes[0];
  var i := 1;
  while i < |cafes|
    invariant 1 <= i <= |cafes|
    invariant mini in cafes
    invariant forall k :: 0 <= k < i ==> LastOccurrencePosition(cafes, mini) <= LastOccurrencePosition(cafes, cafes[k])
  {
    var min_last_pos := LastOccurrencePosition(cafes, mini);
    var current_last_pos := LastOccurrencePosition(cafes, cafes[i]);
    if current_last_pos < min_last_pos {
      mini := cafes[i];
    }
    i := i + 1;
  }
}
// </vc-code>

