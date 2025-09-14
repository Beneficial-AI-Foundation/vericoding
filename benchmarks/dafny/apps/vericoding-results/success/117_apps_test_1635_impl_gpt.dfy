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
  requires cafe in cafes
  requires 0 <= i < |cafes|
  requires exists j :: 0 <= j <= i && cafes[j] == cafe
  ensures 0 <= LastOccurrenceHelper(cafes, cafe, i) < |cafes|
  ensures cafes[LastOccurrenceHelper(cafes, cafe, i)] == cafe
  ensures forall j :: LastOccurrenceHelper(cafes, cafe, i) < j <= i ==> cafes[j] != cafe
  decreases i + 1
{
  if cafes[i] == cafe then
    i
  else
    LastOccurrenceHelper(cafes, cafe, i - 1)
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
  var i := 1;
  mini := cafes[0];
  assert mini in cafes;
  var minPos := LastOccurrencePosition(cafes, mini);
  while i < |cafes|
    invariant 1 <= i <= |cafes|
    invariant mini in cafes
    invariant minPos == LastOccurrencePosition(cafes, mini)
    invariant 0 <= minPos < |cafes|
    invariant forall cafe :: (exists j :: 0 <= j < i && cafes[j] == cafe) ==> LastOccurrencePosition(cafes, mini) <= LastOccurrencePosition(cafes, cafe)
    decreases |cafes| - i
  {
    var c := cafes[i];
    assert c in cafes;
    var p := LastOccurrencePosition(cafes, c);
    if p < minPos {
      mini := c;
      minPos := p;
    }
    i := i + 1;
  }
}
// </vc-code>

