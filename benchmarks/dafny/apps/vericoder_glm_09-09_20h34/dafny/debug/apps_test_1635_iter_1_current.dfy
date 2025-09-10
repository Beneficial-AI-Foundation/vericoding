function LastOccurrencePosition(cafes: seq<int>, cafe: int): int
    requires cafe in cafes
    ensures 0 <= LastOccurrencePosition(cafes, cafe) < |cafes|
    ensures cafes[LastOccurrencePosition(cafes, cafe)] == cafe
    ensures forall j :: LastOccurrencePosition(cafes, cafe) < j < |cafes| ==> cafes[j] != cafe
{
    LastOccurrenceHelper(cafes, cafe, |cafes| - 1)
}

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method solve(cafes: seq<int>) returns (mini: int)
    requires |cafes| > 0
    ensures mini in cafes
    ensures forall cafe :: cafe in cafes ==> LastOccurrencePosition(cafes, mini) <= LastOccurrencePosition(cafes, cafe)
// </vc-spec>
// <vc-code>
{
  var mini := cafes[0];
  var minPos := LastOccurrencePosition(cafes, mini);
  var i := 1;

  while i < |cafes|
      invariant 0 <= i <= |cafes|
      invariant mini in cafes[0..i]
      invariant minPos == LastOccurrencePosition(cafes, mini)
      invariant forall k :: 0 <= k < i ==> minPos <= LastOccurrencePosition(cafes, cafes[k])
  {
      var current := cafes[i];
      var currentPos := LastOccurrencePosition(cafes, current);
      if currentPos < minPos {
          mini := current;
          minPos := currentPos;
      }
      i := i + 1;
  }

  return mini;
}
// </vc-code>

