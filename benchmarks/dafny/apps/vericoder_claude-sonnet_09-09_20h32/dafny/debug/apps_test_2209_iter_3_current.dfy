predicate ValidInput(input: seq<string>)
{
    |input| >= 1 &&
    (forall i :: 0 <= i < |input[0]| ==> '0' <= input[0][i] <= '9') &&
    var n := StringToInt(input[0]);
    n >= 1 && |input| >= n + 1 &&
    forall i :: 1 <= i <= n ==> (|input[i]| > 0 &&
        forall j :: 0 <= j < |input[i]| ==> input[i][j] == 's' || input[i][j] == 'h')
}

function StringToInt(s: string): int
    requires forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
    ensures StringToInt(s) >= 0
{
    if |s| == 0 then 0
    else StringToInt(s[..|s|-1]) * 10 + (s[|s|-1] as int - '0' as int)
}

function CountChar(s: string, c: char): int
    ensures CountChar(s, c) >= 0
    ensures CountChar(s, c) <= |s|
{
    if |s| == 0 then 0
    else (if s[0] == c then 1 else 0) + CountChar(s[1..], c)
}

function CountShSubsequences(s: string): int
    ensures CountShSubsequences(s) >= 0
{
    CountShSubsequencesHelper(s, 0, 0)
}

function CountShSubsequencesHelper(s: string, index: int, s_count: int): int
    requires 0 <= index <= |s|
    requires s_count >= 0
    ensures CountShSubsequencesHelper(s, index, s_count) >= 0
    decreases |s| - index
{
    if index == |s| then 0
    else if s[index] == 's' then
        CountShSubsequencesHelper(s, index + 1, s_count + 1)
    else if s[index] == 'h' then
        s_count + CountShSubsequencesHelper(s, index + 1, s_count)
    else
        CountShSubsequencesHelper(s, index + 1, s_count)
}

function StringRatio(s: string): real
    requires |s| > 0
{
    (CountChar(s, 's') as real) / (|s| as real)
}

function ConcatenateStrings(strings: seq<string>): string
{
    if |strings| == 0 then ""
    else strings[0] + ConcatenateStrings(strings[1..])
}

predicate IsSortedByRatio(strings: seq<string>)
    requires forall i :: 0 <= i < |strings| ==> |strings[i]| > 0
{
    forall i, j :: 0 <= i < j < |strings| ==> StringRatio(strings[i]) <= StringRatio(strings[j])
}

predicate IsValidArrangement(original: seq<string>, arranged: seq<string>)
{
    |arranged| == |original| && multiset(arranged) == multiset(original)
}

// <vc-helpers>
lemma ConcatenatePreservesContent(strings: seq<string>)
    ensures forall c :: CountChar(ConcatenateStrings(strings), c) == 
            Sum(seq(|strings|, i requires 0 <= i < |strings| => CountChar(strings[i], c)))
{
    if |strings| == 0 {
    } else {
        ConcatenatePreservesContent(strings[1..]);
        ConcatenateTwoStringsPreservesCount(strings[0], ConcatenateStrings(strings[1..]), 's');
        ConcatenateTwoStringsPreservesCount(strings[0], ConcatenateStrings(strings[1..]), 'h');
    }
}

lemma ConcatenateTwoStringsPreservesCount(s1: string, s2: string, c: char)
    ensures CountChar(s1 + s2, c) == CountChar(s1, c) + CountChar(s2, c)
{
    if |s1| == 0 {
    } else {
        ConcatenateTwoStringsPreservesCount(s1[1..], s2, c);
    }
}

function Sum(s: seq<int>): int
{
    if |s| == 0 then 0 else s[0] + Sum(s[1..])
}

lemma SortingPreservesMultiset(strings: seq<string>) returns (sorted: seq<string>)
    requires forall i :: 0 <= i < |strings| ==> |strings[i]| > 0
    ensures |sorted| == |strings|
    ensures multiset(sorted) == multiset(strings)
    ensures IsSortedByRatio(sorted)
{
    sorted := SortByRatio(strings);
}

function SortByRatio(strings: seq<string>): seq<string>
    requires forall i :: 0 <= i < |strings| ==> |strings[i]| > 0
    ensures |SortByRatio(strings)| == |strings|
    ensures multiset(SortByRatio(strings)) == multiset(strings)
    ensures IsSortedByRatio(SortByRatio(strings))
{
    if |strings| <= 1 then strings
    else 
        var pivot := strings[0];
        var left := seq s | s in strings[1..] && StringRatio(s) <= StringRatio(pivot) :: s;
        var right := seq s | s in strings[1..] && StringRatio(s) > StringRatio(pivot) :: s;
        SortByRatio(left) + [pivot] + SortByRatio(right)
}
// </vc-helpers>

// <vc-spec>
method solve(input: seq<string>) returns (result: int)
    requires ValidInput(input)
    ensures result >= 0
// </vc-spec>
// <vc-code>
{
    var n := StringToInt(input[0]);
    var strings := input[1..n+1];
    
    var sortedStrings := SortByRatio(strings);
    SortingPreservesMultiset(strings);
    
    var concatenated := ConcatenateStrings(sortedStrings);
    ConcatenatePreservesContent(sortedStrings);
    
    result := CountShSubsequences(concatenated);
}
// </vc-code>

