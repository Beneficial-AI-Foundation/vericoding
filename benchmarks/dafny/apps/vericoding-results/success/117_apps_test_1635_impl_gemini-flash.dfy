// <vc-preamble>
function LastOccurrencePosition(cafes: seq<int>, cafe: int): int
    requires cafe in cafes
    ensures 0 <= LastOccurrencePosition(cafes, cafe) < |cafes|
    ensures cafes[LastOccurrencePosition(cafes, cafe)] == cafe
    ensures forall j :: LastOccurrencePosition(cafes, cafe) < j < |cafes| ==> cafes[j] != cafe
{
    LastOccurrenceHelper(cafes, cafe, |cafes| - 1)
}
// </vc-preamble>

// <vc-helpers>
function LastOccurrenceHelper(cafes: seq<int>, cafe: int, index: int): int
    requires 0 <= index < |cafes|
    requires cafe in cafes[..index+1]
    ensures 0 <= LastOccurrenceHelper(cafes, cafe, index) < |cafes|
    ensures cafes[LastOccurrenceHelper(cafes, cafe, index)] == cafe
    ensures forall j :: LastOccurrenceHelper(cafes, cafe, index) < j <= index ==> cafes[j] != cafe
{
    if cafes[index] == cafe then index else LastOccurrenceHelper(cafes, cafe, index - 1)
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
    invariant mini in cafes[..i]
    invariant forall cafe_iter :: cafe_iter in cafes[..i] ==> LastOccurrencePosition(cafes, mini) <= LastOccurrencePosition(cafes, cafe_iter)
  {
    if LastOccurrencePosition(cafes, cafes[i]) < LastOccurrencePosition(cafes, mini) {
      mini := cafes[i];
    }
    i := i + 1;
  }
}
// </vc-code>
