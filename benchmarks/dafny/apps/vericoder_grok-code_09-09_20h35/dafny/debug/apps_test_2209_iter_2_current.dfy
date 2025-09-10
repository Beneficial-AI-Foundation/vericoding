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
method SortByRatio(strings: seq<string>) returns (sorted: seq<string>)
    requires forall i :: 0 <= i < |strings| ==> |strings[i]| > 0
    ensures |sorted| == |strings|
    ensures multiset(strings) == multiset(sorted)
    ensures IsSortedByRatio(sorted)
{
    sorted := [];
    for i := 0 to |strings|
        invariant |sorted| == i
        invariant multiset(strings[..i]) == multiset(sorted)
        invariant forall j :: 0 <= j < |sorted| ==> |sorted[j]| > 0
        invariant IsSortedByRatio(sorted)
    {
        var newelement := strings[i];
        var pos := 0;
        while pos < |sorted| && StringRatio(sorted[pos]) <= StringRatio(newelement)
            invariant 0 <= pos <= |sorted|
            invariant forall j :: 0 <= j < |sorted| ==> |sorted[j]| > 0
            invariant forall k :: 0 <= k < pos ==> StringRatio(sorted[k]) <= StringRatio(newelement)
            invariant pos == |sorted| ==> forall k :: 0 <= k < |sorted| ==> StringRatio(sorted[k]) <= StringRatio(newelement)
            invariant pos < |sorted| ==> forall k :: 0 <= k < |sorted| ==> (k < pos ==> StringRatio(sorted[k]) <= StringRatio(newelement)) && (k >= pos ==> StringRatio(sorted[k]) > StringRatio(newelement))
        {
            pos := pos + 1;
        }
        sorted := sorted[..pos] + [newelement] + sorted[pos..];
    }
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
    var strings := input[1 .. n+1];
    var sorted := SortByRatio(strings);
    var concatenated := ConcatenateStrings(sorted);
    result := CountShSubsequences(concatenated);
}
// </vc-code>

