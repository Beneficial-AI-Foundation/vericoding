// <vc-helpers>
lemma MaxListExists(lists: seq<seq<int>>) 
    requires |lists| > 0
    ensures exists i :: 0 <= i < |lists| && forall j :: 0 <= j < |lists| ==> |lists[j]| <= |lists[i]|
{
    var maxIndex := FindMaxIndex(lists, 0, 0);
    assert 0 <= maxIndex < |lists|;
    assert forall j :: 0 <= j < |lists| ==> |lists[j]| <= |lists[maxIndex]|;
}

function FindMaxIndex(lists: seq<seq<int>>, currentIndex: int, maxIndex: int): int
    requires |lists| > 0
    requires 0 <= currentIndex <= |lists|
    requires 0 <= maxIndex < |lists|
    requires forall j :: 0 <= j < currentIndex ==> |lists[j]| <= |lists[maxIndex]|
    ensures 0 <= FindMaxIndex(lists, currentIndex, maxIndex) < |lists|
    ensures forall j :: 0 <= j < currentIndex + (|lists| - currentIndex) ==> |lists[j]| <= |lists[FindMaxIndex(lists, currentIndex, maxIndex)]|
    decreases |lists| - currentIndex
{
    if currentIndex == |lists| then
        maxIndex
    else if |lists[currentIndex]| > |lists[maxIndex]| then
        FindMaxIndex(lists, currentIndex + 1, currentIndex)
    else
        FindMaxIndex(lists, currentIndex + 1, maxIndex)
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
method MaxLengthList(lists: seq<seq<int>>) returns (maxList: seq<int>)
    requires |lists| > 0
    ensures forall l :: l in lists ==> |l| <= |maxList|
    ensures maxList in lists
// </vc-spec>
// </vc-spec>

// <vc-code>
{
    var maxIndex := 0;
    var i := 1;
    
    while i < |lists|
        invariant 0 <= i <= |lists|
        invariant 0 <= maxIndex < |lists|
        invariant forall j :: 0 <= j < i ==> |lists[j]| <= |lists[maxIndex]|
    {
        if |lists[i]| > |lists[maxIndex]| {
            maxIndex := i;
        }
        i := i + 1;
    }
    
    maxList := lists[maxIndex];
}
// </vc-code>
