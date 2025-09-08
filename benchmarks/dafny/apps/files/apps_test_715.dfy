Given a multiple-choice question with four options (A, B, C, D), predict a child's choice.
Calculate the length of each option's description (excluding prefix "A.", "B.", etc.).
A choice is "great" if its description is either at least twice shorter than all others
OR at least twice longer than all others. If exactly one choice is great, select it.
Otherwise, select choice C.

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
        assert '\n' !in line;
        if end < |s| then SplitLinesHelper(s, end + 1, acc + [line])
        else acc + [line]
}

function FindNextNewline(s: string, start: int): int
    requires 0 <= start <= |s|
    ensures start <= FindNextNewline(s, start) <= |s|
    ensures FindNextNewline(s, start) == |s| || s[FindNextNewline(s, start)] == '\n'
    ensures forall i :: start <= i < FindNextNewline(s, start) ==> s[i] != '\n'
    decreases |s| - start
{
    if start >= |s| then |s|
    else if s[start] == '\n' then start
    else FindNextNewline(s, start + 1)
}

function SortPairsFunc(pairs: seq<(int, int)>): seq<(int, int)>
    ensures |SortPairsFunc(pairs)| == |pairs|
    ensures forall i, j :: 0 <= i < j < |SortPairsFunc(pairs)| ==> SortPairsFunc(pairs)[i].0 <= SortPairsFunc(pairs)[j].0
    ensures forall p :: p in SortPairsFunc(pairs) <==> p in pairs
    ensures forall p :: p in pairs ==> (exists q :: q in SortPairsFunc(pairs) && q == p)
    ensures (forall p :: p in pairs ==> p.1 in {0, 1, 2, 3}) ==> (forall q :: q in SortPairsFunc(pairs) ==> q.1 in {0, 1, 2, 3})
    decreases |pairs|
{
    if |pairs| <= 1 then pairs
    else
        var pivot := pairs[0];
        var rest := pairs[1..];
        var smaller := FilterSmallerOrEqual(rest, pivot.0);
        var larger := FilterLarger(rest, pivot.0);

        PartitionComplete(rest, pivot.0);

        var sortedSmaller := SortPairsFunc(smaller);
        var sortedLarger := SortPairsFunc(larger);

        sortedSmaller + [pivot] + sortedLarger
}

function FilterSmallerOrEqual(pairs: seq<(int, int)>, pivotValue: int): seq<(int, int)>
    ensures |FilterSmallerOrEqual(pairs, pivotValue)| <= |pairs|
    ensures forall p :: p in FilterSmallerOrEqual(pairs, pivotValue) ==> p in pairs
    ensures forall p :: p in FilterSmallerOrEqual(pairs, pivotValue) ==> p.0 <= pivotValue
    decreases |pairs|
{
    if |pairs| == 0 then []
    else if pairs[0].0 <= pivotValue then [pairs[0]] + FilterSmallerOrEqual(pairs[1..], pivotValue)
    else FilterSmallerOrEqual(pairs[1..], pivotValue)
}

function FilterLarger(pairs: seq<(int, int)>, pivotValue: int): seq<(int, int)>
    ensures |FilterLarger(pairs, pivotValue)| <= |pairs|
    ensures forall p :: p in FilterLarger(pairs, pivotValue) ==> p in pairs
    ensures forall p :: p in FilterLarger(pairs, pivotValue) ==> p.0 > pivotValue
    decreases |pairs|
{
    if |pairs| == 0 then []
    else if pairs[0].0 > pivotValue then [pairs[0]] + FilterLarger(pairs[1..], pivotValue)
    else FilterLarger(pairs[1..], pivotValue)
}

lemma PartitionComplete(pairs: seq<(int, int)>, pivotValue: int)
    ensures |FilterSmallerOrEqual(pairs, pivotValue)| + |FilterLarger(pairs, pivotValue)| == |pairs|
    ensures forall p :: p in FilterSmallerOrEqual(pairs, pivotValue) ==> p in pairs
    ensures forall p :: p in FilterLarger(pairs, pivotValue) ==> p in pairs
    ensures forall p :: p in pairs ==> p in FilterSmallerOrEqual(pairs, pivotValue) || p in FilterLarger(pairs, pivotValue)
{
    if |pairs| == 0 {
        // Base case
    } else {
        PartitionComplete(pairs[1..], pivotValue);
    }
}

method SortPairs(pairs: array<(int, int)>)
    modifies pairs
    requires pairs.Length == 4
    requires forall j :: 0 <= j < pairs.Length ==> pairs[j].1 in {0, 1, 2, 3}
    ensures forall i, j :: 0 <= i < j < pairs.Length ==> pairs[i].0 <= pairs[j].0
    ensures forall i :: 0 <= i < pairs.Length ==> pairs[i].1 in {0, 1, 2, 3}
{
    var i := 0;
    while i < 4
        invariant 0 <= i <= 4
        invariant forall k, l :: 0 <= k < l < i ==> pairs[k].0 <= pairs[l].0
        invariant forall k :: i <= k < 4 ==> forall l :: 0 <= l < i ==> pairs[l].0 <= pairs[k].0
        invariant forall j :: 0 <= j < pairs.Length ==> pairs[j].1 in {0, 1, 2, 3}
    {
        var minIdx := i;
        var j := i + 1;
        while j < 4
            invariant i <= minIdx < 4
            invariant i + 1 <= j <= 4
            invariant forall k :: i <= k < j ==> pairs[minIdx].0 <= pairs[k].0
            invariant forall k :: 0 <= k < pairs.Length ==> pairs[k].1 in {0, 1, 2, 3}
        {
            if pairs[j].0 < pairs[minIdx].0 {
                minIdx := j;
            }
            j := j + 1;
        }
        if minIdx != i {
            var temp := pairs[i];
            pairs[i] := pairs[minIdx];
            pairs[minIdx] := temp;
        }
        i := i + 1;
    }
}

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
{
    var lines := SplitLines(input);
    if |lines| < 4 {
        return "C";
    }

    // Calculate lengths (minus 2 for prefix like "A.")
    var lengths := [|lines[0]| - 2, |lines[1]| - 2, |lines[2]| - 2, |lines[3]| - 2];
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
