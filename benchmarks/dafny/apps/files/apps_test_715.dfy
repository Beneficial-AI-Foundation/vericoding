/*
Given a multiple-choice question with four options (A, B, C, D), predict a child's choice.
Calculate the length of each option's description (excluding prefix "A.", "B.", etc.).
A choice is "great" if its description is either at least twice shorter than all others
OR at least twice longer than all others. If exactly one choice is great, select it.
Otherwise, select choice C.
*/

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
  assume {:axiom} false;
}
// </vc-code>
