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
function SplitLinesHelper(s: string, i: int, acc: seq<string>): seq<string>
    requires 0 <= i <= |s|
    ensures forall line :: line in SplitLinesHelper(s, i, acc) ==> '\n' !in line
{
    if i >= |s| then acc
    else
        var j := i;
        while j < |s| && s[j] != '\n'
            invariant i <= j <= |s|
            invariant forall k :: i <= k < j ==> s[k] != '\n'
        {
            j := j + 1;
        }
        var line := s[i..j];
        var new_acc := acc + [line];
        if j < |s| && s[j] == '\n' then
            SplitLinesHelper(s, j+1, new_acc)
        else
            new_acc
}

function SortPairsFunc(pairs: seq<(int, int)>): seq<(int, int)>
    requires |pairs| == 4
    ensures |SortPairsFunc(pairs)| == 4
    ensures forall i :: 0 <= i < 4 ==> SortPairsFunc(pairs)[i].1 in {0, 1, 2, 3}
    ensures forall i, j :: 0 <= i < j < 4 ==> SortPairsFunc(pairs)[i].0 <= SortPairsFunc(pairs)[j].0
{
    var p0 := pairs[0];
    var p1 := pairs[1];
    var p2 := pairs[2];
    var p3 := pairs[3];
    
    // Bubble sort implementation
    var arr := [p0, p1, p2, p3];
    var swapped := true;
    var n := 4;
    while swapped
        invariant 0 <= n <= 4
        invariant |arr| == 4
    {
        swapped := false;
        var i := 0;
        while i < n-1
            invariant 0 <= i <= n-1 <= 3
        {
            if arr[i].0 > arr[i+1].0 {
                var temp := arr[i];
                arr := arr[..i] + [arr[i+1]] + [arr[i]] + arr[i+2..];
                swapped := true;
            }
            i := i + 1;
        }
        n := n - 1;
    }
    arr
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
    
    var l0 := |lines[0]|;
    var l1 := |lines[1]|;
    var l2 := |lines[2]|;
    var l3 := |lines[3]|;
    
    var lengths := [l0 - 2, l1 - 2, l2 - 2, l3 - 2];
    var sortedPairs := SortLengthsWithIndices(lengths);
    
    var shortest := sortedPairs[0].0;
    var second := sortedPairs[1].0;
    var third := sortedPairs[2].0;
    var longest := sortedPairs[3].0;
    
    var shortestTwiceShorter := shortest * 2 <= second;
    var longestTwiceLonger := longest >= third * 2;
    
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

