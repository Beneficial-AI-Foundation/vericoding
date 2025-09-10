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
    requires forall i :: 0 <= i < index ==> s[i] <= currentMax
    decreases |s| - index
    ensures forall i :: 0 <= i < |s| ==> s[i] <= MaxInSeqIter(s, 0, s[0])
    ensures exists i :: 0 <= i < |s| && s[i] == MaxInSeqIter(s, 0, s[0])
    ensures index == |s| ==> currentMax == MaxInSeqIter(s, 0, s[0])
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
        var nextMax := MaxInSeqIter(s, 1, s[0]);

        // Prove relationship between MaxInSeq and MaxInSeqIter for the tail
        MaxInSeqProperties(s[1..]);
        assert MaxInSeq(s[1..]) == MaxInSeqIter(s[1..], 0, s[1]);

        // Connect MaxInSeqIter calls
        if s[0] >= tailMax {
            calc {
                MaxInSeq(s);
                s[0];
            }
            if s[0] >= MaxInSeqIter(s[1..], 0, s[1]) {
                assert MaxInSeqIter(s, 0, s[0]) == MaxInSeqIter(s, 1, s[0]);
                assert MaxInSeqIter(s, 1, s[0]) == MaxInSeqIter(s[1..], 0, s[0]);
                assert (if s[0] > MaxInSeqIter(s[1..], 0, s[1]) then s[0] else MaxInSeqIter(s[1..], 0, s[1])) == s[0];
                calc {
                    MaxInSeqIter(s, 0, s[0]);
                    MaxInSeqIter(s, 1, s[0]); // Base case from recursive definition
                    // Specifically, MaxInSeqIter(s, 0, s[0]) will recursively call MaxInSeqIter(s, 1, s[0]), using s[0] as currentMax
                    // The sequence s[1..] is passed to MaxInSeqIter, starting from index 0 with initial max s[1]
                    // We need to relate MaxInSeqIter(s, 0, s[0]) with MaxInSeqIter(s[1..], 0, s[1])
                }
                // Consider the definition of MaxInSeqIter:
                // MaxInSeqIter(s, 0, s[0]): compares s[0] with the max of s[1..].
                // The current iteration's max is s[0]. Next call is MaxInSeqIter(s, 1, s[0] if s[0] > s[0] else s[0])
                // which is MaxInSeqIter(s, 1, s[0]).
                // This continues, so MaxInSeqIter(s, 0, s[0]) is effectively the max of s[0] and MaxInSeqIter(s[1..], 0, s[1]).
                assert MaxInSeqIter(s, 0, s[0]) == (if s[0] > MaxInSeqIter(s[1..], 0, s[1]) then s[0] else MaxInSeqIter(s[1..], 0, s[1]));
                assert s[0] == MaxInSeqIter(s, 0, s[0]);
            } else {
                calc {
                    MaxInSeq(s);
                    tailMax;
                }
                assert tailMax == MaxInSeqIter(s[1..], 0, s[1]);
                assert (if s[0] > MaxInSeqIter(s[1..], 0, s[1]) then s[0] else MaxInSeqIter(s[1..], 0, s[1])) == MaxInSeqIter(s[1..], 0, s[1]);
                assert tailMax == MaxInSeqIter(s, 0, s[0]);
            }
        } else {
            calc {
                MaxInSeq(s);
                tailMax;
            }
            assert tailMax == MaxInSeqIter(s[1..], 0, s[1]);
            assert (if s[0] > MaxInSeqIter(s[1..], 0, s[1]) then s[0] else MaxInSeqIter(s[1..], 0, s[1])) == MaxInSeqIter(s[1..], 0, s[1]);
            assert MaxInSeqIter(s, 0, s[0]) == MaxInSeqIter(s[1..], 0, s[1]);
            assert MaxInSeqIter(s, 0, s[0]) == tailMax;
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

    // Loop invariant:
    // 0 <= i <= n
    // forall k :: 0 <= k < i ==> heights[k] <= currentMax
    // exists k :: 0 <= k < i && heights[k] == currentMax
    while i < n
        invariant 0 <= i <= n
        invariant forall k :: 0 <= k < i ==> heights[k] <= currentMax
        invariant exists k :: 0 <= k < i && heights[k] == currentMax
        decreases n - i
    {
        if heights[i] > currentMax {
            currentMax := heights[i];
        }
        i := i + 1;
    }
    result := currentMax;

    // Prove that result is indeed MaxInSeq(heights)
    // We can use the MaxInSeqIter function defined in helpers and prove its equivalence to MaxInSeq.
    // The loop computes MaxInSeqIter(heights, 0, heights[0]).
    // We need to show that currentMax at the end of the loop is MaxInSeqIter(heights, 0, heights[0]).
    // Initial state: i=1, currentMax = heights[0].
    // MaxInSeqIter(s, index, currentMax) is called with index = |s|, currentMax as max of s[0..|s|-1] at the beginning,
    // MaxInSeqIter(heights, 0, heights[0]) is the true maximum.
    // The invariant implies that at loop termination (i == n):
    // forall k :: 0 <= k < n ==> heights[k] <= currentMax (which is 'result')
    // exists k :: 0 <= k < n && heights[k] == currentMax (which is 'result')
    // These two properties are part of ValidResult and also consequences of MaxInSeq.
    // To connect to MaxInSeq, we need the lemma MaxInSeqProperties.
    MaxInSeqProperties(heights);
    assert result == MaxInSeq(heights); // This is inferred by Dafny due to the loop invariant matching properties of MaxInSeq
}
// </vc-code>

