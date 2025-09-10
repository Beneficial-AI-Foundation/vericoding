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
        var end := FindNextNewline(s, start);
        var line := s[start..end];
        if end < |s| then SplitLinesHelper(s, end + 1, acc + [line])
        else acc + [line]
}

function FindNextNewline(s: string, start: int): int
    requires 0 <= start <= |s|
    ensures start <= FindNextNewline(s, start) <= |s|
    ensures FindNextNewline(s, start) == |s| || s[FindNextNewline(s, start)] == '\n'
    decreases |s| - start
{
    if start >= |s| then |s|
    else if s[start] == '\n' then start
    else FindNextNewline(s, start + 1)
}

function SortPairsFunc(pairs: seq<(int, int)>): seq<(int, int)>
    requires |pairs| == 4
    ensures |SortPairsFunc(pairs)| == 4
    ensures forall i :: 0 <= i < 4 ==> SortPairsFunc(pairs)[i] in pairs
    ensures forall i, j :: 0 <= i < j < 4 ==> SortPairsFunc(pairs)[i].0 <= SortPairsFunc(pairs)[j].0
{
    var step1 := if pairs[0].0 > pairs[1].0 then [pairs[1], pairs[0], pairs[2], pairs[3]] else pairs;
    var step2 := if step1[1].0 > step1[2].0 then [step1[0], step1[2], step1[1], step1[3]] else step1;
    var step3 := if step2[2].0 > step2[3].0 then [step2[0], step2[1], step2[3], step2[2]] else step2;
    var step4 := if step3[0].0 > step3[1].0 then [step3[1], step3[0], step3[2], step3[3]] else step3;
    var step5 := if step4[1].0 > step4[2].0 then [step4[0], step4[2], step4[1], step4[3]] else step4;
    var step6 := if step5[0].0 > step5[1].0 then [step5[1], step5[0], step5[2], step5[3]] else step5;
    step6
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
        result := "C";
    } else {
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
}
// </vc-code>

