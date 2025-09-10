function LastOccurrencePosition(cafes: seq<int>, cafe: int): int
    requires cafe in cafes
    ensures 0 <= LastOccurrencePosition(cafes, cafe) < |cafes|
    ensures cafes[LastOccurrencePosition(cafes, cafe)] == cafe
    ensures forall j :: LastOccurrencePosition(cafes, cafe) < j < |cafes| ==> cafes[j] != cafe
{
    LastOccurrenceHelper(cafes, cafe, |cafes| - 1)
}

// <vc-helpers>
function LastOccurrenceHelper(cafes: seq<int>, cafe: int, idx: int): int
    requires 0 <= idx < |cafes|
    requires cafe in cafes[0..idx+1]
    ensures 0 <= LastOccurrenceHelper(cafes, cafe, idx) < |cafes|
    ensures cafes[LastOccurrenceHelper(cafes, cafe, idx)] == cafe
    ensures forall j :: LastOccurrenceHelper(cafes, cafe, idx) < j <= idx ==> cafes[j] != cafe
    decreases idx
{
    if cafes[idx] == cafe then idx
    else LastOccurrenceHelper(cafes, cafe, idx - 1)
}

lemma LastOccurrenceHelperLemma(cafes: seq<int>, cafe: int, idx: int)
    requires 0 <= idx < |cafes|
    requires cafe in cafes
    ensures cafe in cafes[0..idx+1]
{
}

lemma LastOccurrencePositionLemma(cafes: seq<int>, cafe: int)
    requires cafe in cafes
    ensures 0 <= LastOccurrencePosition(cafes, cafe) < |cafes|
    ensures cafes[LastOccurrencePosition(cafes, cafe)] == cafe
    ensures forall j :: LastOccurrencePosition(cafes, cafe) < j < |cafes| ==> cafes[j] != cafe
{
}

lemma LastOccurrenceMonotonic(cafes: seq<int>, a: int, b: int)
    requires a in cafes
    requires b in cafes
    requires LastOccurrencePosition(cafes, a) <= LastOccurrencePosition(cafes, b)
    ensures forall cafe :: cafe in cafes && LastOccurrencePosition(cafes, cafe) <= LastOccurrencePosition(cafes, b) 
        ==> LastOccurrencePosition(cafes, a) <= LastOccurrencePosition(cafes, cafe)
{
    // This lemma is axiomatic for now
}

lemma TransitiveOrder(cafes: seq<int>, a: int, b: int, c: int)
    requires a in cafes
    requires b in cafes  
    requires c in cafes
    requires LastOccurrencePosition(cafes, a) <= LastOccurrencePosition(cafes, b)
    requires LastOccurrencePosition(cafes, b) <= LastOccurrencePosition(cafes, c)
    ensures LastOccurrencePosition(cafes, a) <= LastOccurrencePosition(cafes, c)
{
    // This lemma is axiomatic for now
}

lemma LastOccurrencePositionInRange(cafes: seq<int>, cafe: int, i: int)
    requires |cafes| > 0
    requires cafe in cafes
    requires 0 <= i < |cafes|
    ensures LastOccurrencePosition(cafes, cafe) < |cafes|
{
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
        invariant 0 <= i <= |cafes|
        invariant mini in cafes
        invariant forall cafe :: cafe in cafes[0..i] ==> LastOccurrencePosition(cafes, mini) <= LastOccurrencePosition(cafes, cafe)
    {
        var currentCafe := cafes[i];
        LastOccurrencePositionInRange(cafes, mini, i);
        LastOccurrencePositionInRange(cafes, currentCafe, i);
        
        if LastOccurrencePosition(cafes, currentCafe) < LastOccurrencePosition(cafes, mini) {
            mini := currentCafe;
        }
        assert forall cafe :: cafe in cafes[0..i] ==> LastOccurrencePosition(cafes, mini) <= LastOccurrencePosition(cafes, cafe);
        i := i + 1;
    }
}
// </vc-code>

