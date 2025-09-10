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
    requires -1 <= i < |cafes|
    ensures 0 <= LastOccurrenceHelper(cafes, cafe, i) <= i + 1 < |cafes|
    ensures i >= 0 ==> LastOccurrenceHelper(cafes, cafe, i) <= i
    ensures cafes[LastOccurrenceHelper(cafes, cafe, i)] == cafe
    ensures forall j :: LastOccurrenceHelper(cafes, cafe, i) < j <= i ==> cafes[j] != cafe
    decreases i + 1
{
    if i == -1 then
        // Since cafe in cafes and we've checked all positions from |cafes|-1 down to 0,
        // there must be at least one occurrence of cafe in cafes[0..|cafes|]
        var k := FindFirstOccurrence(cafes, cafe);
        k
    else if cafes[i] == cafe then
        i
    else
        LastOccurrenceHelper(cafes, cafe, i - 1)
}

function FindFirstOccurrence(cafes: seq<int>, cafe: int): int
    requires cafe in cafes
    ensures 0 <= FindFirstOccurrence(cafes, cafe) < |cafes|
    ensures cafes[FindFirstOccurrence(cafes, cafe)] == cafe
    ensures forall j :: 0 <= j < FindFirstOccurrence(cafes, cafe) ==> cafes[j] != cafe
{
    if cafes[0] == cafe then
        0
    else
        1 + FindFirstOccurrence(cafes[1..], cafe)
}

lemma LastOccurrenceIsUnique(cafes: seq<int>, cafe: int)
    requires cafe in cafes
    ensures exists i :: 0 <= i < |cafes| && cafes[i] == cafe && (forall j :: i < j < |cafes| ==> cafes[j] != cafe)
    ensures forall i1, i2 :: (0 <= i1 < |cafes| && cafes[i1] == cafe && (forall j :: i1 < j < |cafes| ==> cafes[j] != cafe)) &&
                             (0 <= i2 < |cafes| && cafes[i2] == cafe && (forall j :: i2 < j < |cafes| ==> cafes[j] != cafe))
                             ==> i1 == i2
{
    // Find the last occurrence
    var lastIdx := |cafes| - 1;
    while lastIdx >= 0 && cafes[lastIdx] != cafe
        invariant -1 <= lastIdx < |cafes|
        invariant forall j :: lastIdx < j < |cafes| ==> cafes[j] != cafe
        invariant cafe in cafes[0..lastIdx+1]
    {
        lastIdx := lastIdx - 1;
    }
    
    assert lastIdx >= 0;
    assert cafes[lastIdx] == cafe;
    assert forall j :: lastIdx < j < |cafes| ==> cafes[j] != cafe;
    
    // Prove uniqueness
    forall i1, i2 | (0 <= i1 < |cafes| && cafes[i1] == cafe && (forall j :: i1 < j < |cafes| ==> cafes[j] != cafe)) &&
                    (0 <= i2 < |cafes| && cafes[i2] == cafe && (forall j :: i2 < j < |cafes| ==> cafes[j] != cafe))
        ensures i1 == i2
    {
        if i1 != i2 {
            if i1 < i2 {
                assert cafes[i2] != cafe;  // by i1's property
                assert false;
            } else {
                assert cafes[i1] != cafe;  // by i2's property
                assert false;
            }
        }
    }
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
    var miniPos := LastOccurrencePosition(cafes, mini);
    
    var i := 1;
    while i < |cafes|
        invariant 1 <= i <= |cafes|
        invariant mini in cafes
        invariant miniPos == LastOccurrencePosition(cafes, mini)
        invariant forall j :: 0 <= j < i ==> LastOccurrencePosition(cafes, mini) <= LastOccurrencePosition(cafes, cafes[j])
    {
        var currentPos := LastOccurrencePosition(cafes, cafes[i]);
        if currentPos < miniPos {
            mini := cafes[i];
            miniPos := currentPos;
        }
        i := i + 1;
    }
}
// </vc-code>

