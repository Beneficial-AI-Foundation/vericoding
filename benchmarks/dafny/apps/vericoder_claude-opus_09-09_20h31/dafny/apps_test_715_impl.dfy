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
    requires 0 <= start <= |s|
    requires forall line :: line in acc ==> '\n' !in line
    ensures forall line :: line in SplitLinesHelper(s, start, acc) ==> '\n' !in line
    decreases |s| - start
{
    if start >= |s| then acc
    else 
        var end := FindNewline(s, start);
        var line := s[start..end];
        assert '\n' !in line by {
            assert forall i :: start <= i < end ==> s[i] != '\n';
        }
        if end >= |s| then acc + [line]
        else SplitLinesHelper(s, end + 1, acc + [line])
}

function FindNewline(s: string, start: int): int
    requires 0 <= start <= |s|
    ensures start <= FindNewline(s, start) <= |s|
    ensures forall i :: start <= i < FindNewline(s, start) ==> s[i] != '\n'
    ensures FindNewline(s, start) < |s| ==> s[FindNewline(s, start)] == '\n'
    decreases |s| - start
{
    if start >= |s| then |s|
    else if s[start] == '\n' then start
    else FindNewline(s, start + 1)
}

function SortPairsFunc(pairs: seq<(int, int)>): seq<(int, int)>
    requires |pairs| == 4
    ensures |SortPairsFunc(pairs)| == 4
    ensures forall i :: 0 <= i < 4 ==> SortPairsFunc(pairs)[i] in pairs
    ensures forall i, j :: 0 <= i < j < 4 ==> SortPairsFunc(pairs)[i].0 <= SortPairsFunc(pairs)[j].0
{
    var p0, p1, p2, p3 := pairs[0], pairs[1], pairs[2], pairs[3];
    
    // Simple bubble sort for 4 elements
    var (p0, p1) := if p0.0 > p1.0 then (p1, p0) else (p0, p1);
    var (p2, p3) := if p2.0 > p3.0 then (p3, p2) else (p2, p3);
    var (p0, p2) := if p0.0 > p2.0 then (p2, p0) else (p0, p2);
    var (p1, p3) := if p1.0 > p3.0 then (p3, p1) else (p1, p3);
    var (p1, p2) := if p1.0 > p2.0 then (p2, p1) else (p1, p2);
    
    [p0, p1, p2, p3]
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
    }
    
    var lengths := [|lines[0]| - 2, |lines[1]| - 2, |lines[2]| - 2, |lines[3]| - 2];
    var sortedPairs := SortLengthsWithIndices(lengths);
    
    var shortestTwiceShorter := sortedPairs[0].0 * 2 <= sortedPairs[1].0;
    var longestTwiceLonger := sortedPairs[3].0 >= sortedPairs[2].0 * 2;
    
    if shortestTwiceShorter && longestTwiceLonger {
        result := "C";
    } else if shortestTwiceShorter {
        result := ChoiceFromIndex(sortedPairs[0].1);
    } else if longestTwiceLonger {
        result := ChoiceFromIndex(sortedPairs[3].1);
    } else {
        result := "C";
    }
}
// </vc-code>

