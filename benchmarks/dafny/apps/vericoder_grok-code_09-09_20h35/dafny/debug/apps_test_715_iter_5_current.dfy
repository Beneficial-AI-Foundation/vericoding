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
// helper for splitting
function FindEndOfLine(s: string, start: int): int
    requires 0 <= start <= |s|
    ensures start <= FindEndOfLine(s, start) <= |s|
    ensures forall i :: start <= i < FindEndOfLine(s, start) ==> s[i] != '\n'
    ensures FindEndOfLine(s, start) == |s| || s[FindEndOfLine(s, start)] == '\n'
    decreases |s| - start
{
    if start == |s| then start
    else if s[start] == '\n' then start
    else FindEndOfLine(s, start + 1)
}

function SplitLinesHelper(s: string, start: int, acc: seq<string>): seq<string>
    requires 0 <= start <= |s|
    decreases |s| - start
    ensures forall line :: line in SplitLinesHelper(s, start, acc) ==> '\n' !in line
{
    var end := FindEndOfLine(s, start);
    if end == |s| then acc + [s[start..]]
    else acc + [s[start..end]] + SplitLinesHelper(s, end + 1, acc + [s[start..end]])
}

function SortPairsFunc(pairs: seq<(int, int)>): seq<(int, int)>
  requires |pairs| == 4
  requires forall i :: 0 <= i < 4 ==> pairs[i].1 in {0, 1, 2, 3}
  requires forall i, j :: 0 <= i < j < 4 ==> pairs[i].1 != pairs[j].1
  ensures |SortPairsFunc(pairs)| == 4
  ensures forall i :: 0 <= i < 4 ==> SortPairsFunc(pairs)[i].1 in {0, 1, 2, 3}
  ensures forall i, j :: 0 <= i < j < 4 ==> SortPairsFunc(pairs)[i].0 <= SortPairsFunc(pairs)[j].0
  ensures multiset(SortPairsFunc(pairs)) == multiset(pairs)
{
  SelectionSortFunc(pairs, 0, [])
}

function SelectionSortFunc(list: seq<(int, int)>, cur: int, acc: seq<(int, int)>): seq<(int, int)>
  requires |list| == 4 - cur
  requires cur == |acc|
  decreases |list|
  ensures |SelectionSortFunc(list, cur, acc)| == 4 - cur + |acc|
  ensures multiset(SelectionSortFunc(list, cur, acc)) == multiset(acc + list)
{
  if cur == 4 then acc else
    var minIndex := FindMinIndex(list);
    var minElem := list[minIndex];
    SelectionSortFunc(list[..minIndex] + list[minIndex+1..], cur + 1, acc + [minElem])
}

function FindMinIndex(list: seq<(int, int)>): int
  requires |list| > 0
  ensures 0 <= FindMinIndex(list) < |list|
  ensures forall i :: 0 <= i < |list| ==> list[FindMinIndex(list)].0 <= list[i].0
{
  if |list| == 1 then 0 else
    var restMin := FindMinIndex(list[1..]);
    if list[0].0 <= list[restMin + 1].0 then 0 else restMin + 1
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

