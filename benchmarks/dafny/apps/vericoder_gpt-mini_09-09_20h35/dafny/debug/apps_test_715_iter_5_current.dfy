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
function indexOfNewline(s: string, pos: int): int
    requires 0 <= pos <= |s|
    ensures pos <= indexOfNewline(s,pos) <= |s|
    ensures forall k :: pos <= k < indexOfNewline(s,pos) ==> s[k] != '\n'
    ensures indexOfNewline(s,pos) == |s| || s[indexOfNewline(s,pos)] == '\n'
    decreases |s| - pos
{
    if pos == |s| then pos
    else if s[pos] == '\n' then pos
    else indexOfNewline(s, pos + 1)
}

function SplitLinesHelper(s: string, pos: int, acc: seq<string>): seq<string>
    requires 0 <= pos <= |s|
    requires forall line :: line in acc ==> '\n' !in line
    ensures forall line :: line in SplitLinesHelper(s,pos,acc) ==> '\n' !in line
    decreases |s| - pos
{
    if pos == |s| then acc
    else
        var j := indexOfNewline(s, pos);
        var line := s[pos..j];
        // prove that the extracted line contains no newline
        assert forall k :: 0 <= k < |line| ==> line[k] != '\n';
        var newAcc := acc + [line];
        assert forall ln :: ln in newAcc ==> '\n' !in ln;
        if j == |s| then newAcc else SplitLinesHelper(s, j + 1, newAcc)
}

function FirstNonExcluded(excl: set<int>): int
    requires |excl| < 4
    ensures 0 <= FirstNonExcluded(excl) <= 3
    ensures FirstNonExcluded(excl) !in excl
{
    if 0 !in excl then 0
    else if 1 !in excl then 1
    else if 2 !in excl then 2
    else 3
}

function MinIndexExcludingRec(pairs: seq<(int,int)>, excl: set<int>, idx: int, cur: int): int
    requires |pairs| == 4
    requires 0 <= idx <= 4
    requires 0 <= cur <= 3
    requires cur !in excl
    ensures 0 <= MinIndexExcludingRec(pairs, excl, idx, cur) <= 3
    ensures MinIndexExcludingRec(pairs, excl, idx, cur) !in excl
    ensures forall j :: 0 <= j < 4 && j !in excl ==> pairs[MinIndexExcludingRec(pairs, excl, idx, cur)].0 <= pairs[j].0
    decreases 4 - idx
{
    if idx == 4 then cur
    else if idx in excl then MinIndexExcludingRec(pairs, excl, idx + 1, cur)
    else if pairs[idx].0 < pairs[cur].0 then MinIndexExcludingRec(pairs, excl, idx + 1, idx)
    else MinIndexExcludingRec(pairs, excl, idx + 1, cur)
}

function MinIndexExcluding(pairs: seq<(int,int)>, excl: set<int>): int
    requires |pairs| == 4
    requires |excl| < 4
    ensures 0 <= MinIndexExcluding(pairs, excl) <= 3
    ensures MinIndexExcluding(pairs, excl) !in excl
    ensures forall j :: 0 <= j < 4 && j !in excl ==> pairs[MinIndexExcluding(pairs, excl)].0 <= pairs[j].0
    decreases 1
{
    MinIndexExcludingRec(pairs, excl, 0, FirstNonExcluded(excl))
}

function SortPairsFunc(pairs: seq<(int,int)>): seq<(int,int)>
    requires |pairs| == 4
    requires forall i :: 0 <= i < 4 ==> pairs[i].1 in {0,1,2,3}
    ensures |SortPairsFunc(pairs)| == 4
    ensures forall i :: 0 <= i < 4 ==> SortPairsFunc(pairs)[i].1 in {0,1,2,3}
    ensures forall i, j :: 0 <= i < j < 4 ==> SortPairsFunc(pairs)[i].0 <= SortPairsFunc(pairs)[j].0
{
    var i0 := MinIndexExcluding(pairs, {});
    var i1 := MinIndexExcluding(pairs, {i0});
    var i2 := MinIndexExcluding(pairs, {i0, i1});
    var i3 := MinIndexExcluding(pairs, {i0, i1, i2});
    [pairs[i0], pairs[i1], pairs[i2], pairs[i3]]
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
        return;
    }
    var lengths := [|lines[0]| - 2, |lines[1]| - 2, |lines[2]| - 2, |lines[3]| - 2];
    var sortedPairs := SortLengthsWithIndices(lengths);
    var shortestTwiceShorter := sortedPairs[0].0 * 2 <= sortedPairs[1].0;
    var longestTwiceLonger := sortedPairs[3].0 >= sortedPairs[2].0 * 2;
    if shortestTwiceShorter && longestTwiceLonger {
        result := "C";
        return;
    } else if shortestTwiceShorter {
        result := ChoiceFromIndex(sortedPairs[0].1);
        return;
    } else if longestTwiceLonger {
        result := ChoiceFromIndex(sortedPairs[3].1);
        return;
    } else {
        result := "C";
        return;
    }
}
// </vc-code>

