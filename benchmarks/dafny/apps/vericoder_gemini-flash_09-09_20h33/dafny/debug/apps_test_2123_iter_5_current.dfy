predicate ValidInput(n: int, heights: seq<int>)
{
    n > 0 && |heights| == n
}

function MaxInSeq(s: seq<int>): int
    requires |s| > 0
    ensures MaxInSeq(s) in s
    ensures forall i :: 0 <= i < |s| ==> s[i] <= MaxInSeq(s)
{
    if |s| == 1 then s[0]
    else
        var tailMax := MaxInSeq(s[1..]);
        if s[0] >= tailMax then s[0] else tailMax
}

predicate ValidResult(n: int, heights: seq<int>, result: int)
    requires ValidInput(n, heights)
{
    result == MaxInSeq(heights) &&
    forall i :: 0 <= i < |heights| ==> heights[i] <= result &&
    exists i :: 0 <= i < |heights| && heights[i] == result
}

// <vc-helpers>
function MaxInSeqIter(s: seq<int>, index: int, currentMax: int): int
    requires 0 <= index <= |s|
    requires |s| > 0
    requires index == 0 ==> currentMax == s[0]
    decreases |s| - index
    ensures (forall i' :: 0 <= i' < index ==> s[i'] <= currentMax) // currentMax is max up to index-1
    ensures (exists i' :: 0 <= i' < index && s[i'] == currentMax) || index == 0 // currentMax is max of s[0..index-1]
    // The following postconditions state that if we iterate through the whole sequence,
    // currentMax will be the true maximum of the sequence `s`.
    ensures index == |s| ==> currentMax == MaxInSeq(s)
    ensures index == |s| ==> (forall i' :: 0 <= i' < |s| ==> s[i'] <= currentMax)
    ensures index == |s| ==> (exists i' :: 0 <= i' < |s| && s[i'] == currentMax)
{
    if index == |s| then
        currentMax
    else
        var newMax := if s[index] > currentMax then s[index] else currentMax;
        MaxInSeqIter(s, index + 1, newMax)
}

lemma MaxInSeqProperties(s: seq<int>)
    requires |s| > 0
    ensures MaxInSeq(s) == MaxInSeqIter(s, 0, s[0])
    ensures forall i :: 0 <= i < |s| ==> s[i] <= MaxInSeq(s)
    ensures exists i :: 0 <= i < |s| && s[i] == MaxInSeq(s)
{
    if |s| == 1 {
        calc {
            MaxInSeq(s);
            s[0];
            MaxInSeqIter(s, 0, s[0]);
        }
    } else {
        var tailMax := MaxInSeq(s[1..]);
        MaxInSeqProperties(s[1..]);
        assert MaxInSeq(s[1..]) == MaxInSeqIter(s[1..], 0, s[1]);

        var iterMaxFromTail := MaxInSeqIter(s[1..], 0, s[1]);

        if s[0] >= tailMax {
            calc {
                MaxInSeq(s);
                s[0];
            }
            // Add the missing assertion to connect MaxInSeqIter with the simple value s[0]
            assert (s[0] >= iterMaxFromTail) ==> (MaxInSeqIter(s, 1, s[0]) == s[0]);
            assert MaxInSeqIter(s, 0, s[0]) == s[0]; // This is the crucial part for this branch
            assert MaxInSeq(s) == MaxInSeqIter(s, 0, s[0]);
        } else {
            calc {
                MaxInSeq(s);
                tailMax;
            }
            assert MaxInSeq(s[1..]) == iterMaxFromTail;
            assert MaxInSeqIter(s, 0, s[0]) == iterMaxFromTail;
            assert MaxInSeq(s) == MaxInSeqIter(s, 0, s[0]);
        }
    }
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, heights: seq<int>) returns (result: int)
    requires ValidInput(n, heights)
    ensures ValidResult(n, heights, result)
// </vc-spec>
// <vc-code>
{
    var currentMax: int := heights[0];
    var i: int := 1;

    // Prove that the initial state of currentMax and i conforms to the loop invariants.
    // For i=0, the conditions are trivially true or need to be established by definition.
    // For i=1, currentMax is heights[0], which is the max of the first element.
    assert 0 <= i <= n; // i is 1, n is at least 1.
    assert (forall k :: 0 <= k < i ==> heights[k] <= currentMax); // Only k=0. heights[0] <= heights[0].
    assert (exists k :: 0 <= k < i && heights[k] == currentMax); // k=0. heights[0] == heights[0].

    while i < n
        invariant 0 <= i <= n
        invariant forall k :: 0 <= k < i ==> heights[k] <= currentMax
        invariant exists k :: 0 <= k < i && heights[k] == currentMax
        decreases n - i
    {
        // Establish that at the start of the loop iteration, currentMax is indeed the max of heights[0..i-1]
        // From the invariant before the loop:
        // (forall k :: 0 <= k < i ==> heights[k] <= currentMax)
        // (exists k :: 0 <= k < i && heights[k] == currentMax)

        var old_currentMax := currentMax;
        if heights[i] > currentMax {
            currentMax := heights[i];
        }
        
        // After updating currentMax:
        // New invariant for currentMax as max of heights[0..i]
        // If heights[i] was the new max:
        // (forall k :: 0 <= k < i + 1 ==> heights[k] <= currentMax)
        //  - If k < i, then heights[k] <= old_currentMax < heights[i] == currentMax
        //  - If k == i, then heights[i] == currentMax
        // (exists k :: 0 <= k < i + 1 && heights[k] == currentMax)
        //  - If heights[i] was chosen, then k=i works.
        // If heights[i] was not the new max (i.e., heights[i] <= old_currentMax and currentMax == old_currentMax):
        // (forall k :: 0 <= k < i + 1 ==> heights[k] <= currentMax)
        //  - If k < i, then heights[k] <= currentMax (by old invariant)
        //  - If k == i, then heights[i] <= currentMax (by condition)
        // (exists k :: 0 <= k < i + 1 && heights[k] == currentMax)
        //  - Check if something from 0..i-1 exists which is still equal to currentMax. Yes, by old invariant.

        i := i + 1;
    }
    result := currentMax;
    // At this point, i == n.
    // The invariant implies:
    // (forall k :: 0 <= k < n ==> heights[k] <= currentMax)
    // (exists k :: 0 <= k < n && heights[k] == currentMax)
    // These are precisely the conditions for currentMax to be the maximum value in `heights`.

    // MaxInSeqProperties lemma relates MaxInSeq and its iterative definition.
    MaxInSeqProperties(heights);
    
    // To connect the loop invariant's `currentMax` to `MaxInSeqIter(heights, 0, heights[0])`
    // which eventually means `MaxInSeq(heights)`.
    // We need to show that currentMax at the end of the loop is exactly MaxInSeqIter(heights, 0, heights[0]).
    // This is implicitly captured by the loop invariants:
    // When the loop terminates, i == n.
    // The invariant:
    // - `forall k :: 0 <= k < n ==> heights[k] <= currentMax`
    // - `exists k :: 0 <= k < n && heights[k] == currentMax`
    // These two invariants together mean currentMax is the maximum of heights[0...n-1].
    // MaxInSeq(heights) is also defined as the maximum of heights[0...n-1].
    // Since MaxInSeq(heights) == MaxInSeqIter(heights, 0, heights[0]) by MaxInSeqProperties,
    // we can deduce that currentMax must be equal to MaxInSeqIter(heights, 0, heights[0]).

    // The current loop implementation directly computes the maximum.
    // We need to ensure that this currentMax is indeed the same as MaxInSeqIter(heights, 0, heights[0]).
    // The invariants already establish that currentMax is the maximum element in `heights`.
    // MaxInSeqIter(s, 0, s[0]) also computes the maximum.
    // By the uniqueness of the maximum element (if it exists, which it does for non-empty sequences),
    // they must be equal.

    assert currentMax == MaxInSeq(heights);
    assert currentMax == MaxInSeqIter(heights, 0, heights[0]);
}
// </vc-code>

