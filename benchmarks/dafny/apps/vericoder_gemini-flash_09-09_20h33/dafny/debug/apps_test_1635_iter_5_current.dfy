function LastOccurrencePosition(cafes: seq<int>, cafe: int): int
    requires cafe in cafes
    ensures 0 <= LastOccurrencePosition(cafes, cafe) < |cafes|
    ensures cafes[LastOccurrencePosition(cafes, cafe)] == cafe
    ensures forall j :: LastOccurrencePosition(cafes, cafe) < j < |cafes| ==> cafes[j] != cafe
{
    LastOccurrenceHelper(cafes, cafe, |cafes| - 1)
}

// <vc-helpers>
function LastOccurrenceHelper(cafes: seq<int>, cafe: int, index: int): int
    requires 0 <= index < |cafes|
    requires exists i :: 0 <= i <= index && cafes[i] == cafe
    decreases index
    ensures 0 <= LastOccurrenceHelper(cafes, cafe, index) <= index
    ensures cafes[LastOccurrenceHelper(cafes, cafe, index)] == cafe
    ensures forall j :: LastOccurrenceHelper(cafes, cafe, index) < j <= index ==> cafes[j] != cafe
{
    if cafes[index] == cafe then
        index
    else
        LastOccurrenceHelper(cafes, cafe, index - 1)
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
    var minPos := 0;
    var minCafe := cafes[0]; 

    for i := 1 to |cafes| - 1
        invariant 1 <= i <= |cafes|
        invariant 0 <= minPos < i
        invariant minCafe in cafes[0..i]
        invariant minCafe == cafes[minPos]
        invariant forall k :: 0 <= k < i ==> LastOccurrencePosition(cafes, minCafe) <= LastOccurrencePosition(cafes, cafes[k])
    {
        var currentCafe := cafes[i];
        if (LastOccurrencePosition(cafes, currentCafe) < LastOccurrencePosition(cafes, minCafe)) {
            minPos := i;
            minCafe := currentCafe;
        }
    }
    mini := minCafe;
}
// </vc-code>

