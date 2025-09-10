predicate ValidResult(result: string) {
    result in ["A", "B", "C", "D"]
}

function ChoiceFromIndex(index: int): string
    requires 0 <= index <= 3
    ensures ChoiceFromIndex(index) in ["A", "B", "C", "D"]
{
    if index == 0 then "A"
    else if index == 1 then "B"
    else if index == 2 then "C"
    else "D"
}

function SplitLines(s: string): seq<string>
    ensures forall line :: line in SplitLines(s) ==> '\n' !in line
{
    if |s| == 0 then []
    else SplitLinesHelper(s, 0, [])
}

function SortLengthsWithIndices(lengths: seq<int>): seq<(int, int)>
    requires |lengths| == 4
    ensures |SortLengthsWithIndices(lengths)| == 4
    ensures forall i :: 0 <= i < 4 ==> SortLengthsWithIndices(lengths)[i].1 in {0, 1, 2, 3}
    ensures forall i, j :: 0 <= i < j < 4 ==> SortLengthsWithIndices(lengths)[i].0 <= SortLengthsWithIndices(lengths)[j].0
{
    var pairs := [(lengths[0], 0), (lengths[1], 1), (lengths[2], 2), (lengths[3], 3)];
    SortPairsFunc(pairs)
}

// <vc-helpers>
function SplitLinesHelper(s: string, start: int, acc: seq<string>): seq<string>
    decreases |s| - start
    ensures forall line :: line in SplitLinesHelper(s, start, acc) ==> '\n' !in line
{
    if start >= |s| then acc
    else (
        var newlineIndex := start;
        // The original error was `invalid UnaryExpression`. This was due to the while loop's condition, specifically `s[newlineIndex]`.
        // Dafny was inferring `newlineIndex` to be of type `int` without a guarantee that `newlineIndex` is a valid index into `s`.
        // While the loop invariant `newlineIndex <= |s|` is present, it does not guarantee `newlineIndex < |s|` which is required for `s[newlineIndex]`.
        // The fix moves `newlineIndex < |s|` inside the loop condition to ensure the index is always valid before dereferencing s[newlineIndex].
        while newlineIndex < |s| && s[newlineIndex] != '\n'
            invariant start <= newlineIndex <= |s|
            invariant forall k :: start <= k < newlineIndex ==> s[k] != '\n'
        {
            newlineIndex := newlineIndex + 1;
        }

        var line := s[start..newlineIndex];
        if newlineIndex < |s| && s[newlineIndex] == '\n' then // Add check for newlineIndex < |s| for safety
            SplitLinesHelper(s, newlineIndex + 1, acc + [line])
        else
            acc + [line]
    )
}

function SortPairsFunc(a: seq<(int, int)>): (seq<(int, int)>)
    requires |a| == 4
    ensures |SortPairsFunc(a)| == 4
    ensures forall i, j :: 0 <= i < j < 4 ==> SortPairsFunc(a)[i].0 <= SortPairsFunc(a)[j].0
    ensures forall i :: 0 <= i < 4 ==> SortPairsFunc(a)[i].1 in {0, 1, 2, 3}
{
    var b := a;
    for i := 0 to |b| - 2
        invariant 0 <= i < |b|
        invariant |b| == 4
        invariant forall k, l :: 0 <= k < l < i ==> b[k].0 <= b[l].0 // Elements from 0 to i-1 are sorted
        invariant forall k :: 0 <= k < |b| ==> b[k].1 in {0, 1, 2, 3} // Indices remain valid
        invariant multiset(b) == multiset(a) // Permutation of initial elements
    {
        for j := |b| - 1 downto i + 1
            invariant i <= j < |b| // Correct bounds
            invariant |b| == 4
            invariant forall k, l :: 0 <= k < l < i ==> b[k].0 <= b[l].0 // Elements up to i-1 are sorted
            // This invariant was incorrect: forall p, q :: i <= p < q < j ==> b[p].0 <= b[q].0 // elements from i to j-1 are sorted (for this pass for j)
            // It should reflect that elements from j to |b|-1 are sorted relative to each other, and the smallest element from i to j has been bubbled up.
            // A simpler, correct invariant for bubble sort inner loop that doesn't claim sortedness of future elements:
            invariant forall k :: 0 <= k < |b| ==> b[k].1 in {0, 1, 2, 3}
            invariant multiset(b) == multiset(a)
            invariant forall k :: j <= k < |b| ==> b[k].0 >= b[j-1].0 // Elements from j to end are larger than or equal to b[j-1]

        {
            if b[j].0 < b[j-1].0 {
                var temp := b[j];
                b[j] := b[j-1];
                b[j-1] := temp;
            }
        }
    }
    return b;
}
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (result: string)
    requires |input| > 0
    ensures ValidResult(result)
    ensures (var lines := SplitLines(input);
             if |lines| < 4 then result == "C"
             else (
                 var lengths := [|lines[0]| - 2, |lines[1]| - 2, |lines[2]| - 2, |lines[3]| - 2];
                 var sortedPairs := SortLengthsWithIndices(lengths);
                 var shortestTwiceShorter := sortedPairs[0].0 * 2 <= sortedPairs[1].0;
                 var longestTwiceLonger := sortedPairs[3].0 >= sortedPairs[2].0 * 2;
                 if shortestTwiceShorter && longestTwiceLonger then result == "C"
                 else if shortestTwiceShorter then result == ChoiceFromIndex(sortedPairs[0].1)
                 else if longestTwiceLonger then result == ChoiceFromIndex(sortedPairs[3].1)
                 else result == "C"
             ))
// </vc-spec>
// <vc-code>
{
    var lines := SplitLines(input);
    if |lines| < 4 {
        return "C";
    } else {
        var len0 := |lines[0]|;
        var len1 := |lines[1]|;
        var len2 := |lines[2]|;
        var len3 := |lines[3]|;

        var lengths := [len0 - 2, len1 - 2, len2 - 2, len3 - 2];
        
        var sortedPairs := SortLengthsWithIndices(lengths);
        
        var shortestTwiceShorter := sortedPairs[0].0 * 2 <= sortedPairs[1].0;
        var longestTwiceLonger := sortedPairs[3].0 >= sortedPairs[2].0 * 2;

        if shortestTwiceShorter && longestTwiceLonger {
            return "C";
        } else if shortestTwiceShorter {
            return ChoiceFromIndex(sortedPairs[0].1);
        } else if longestTwiceLonger {
            return ChoiceFromIndex(sortedPairs[3].1);
        } else {
            return "C";
        }
    }
}
// </vc-code>

