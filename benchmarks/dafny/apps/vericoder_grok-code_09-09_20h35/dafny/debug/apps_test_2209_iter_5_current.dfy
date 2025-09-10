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
    requires forall i :: 0 <= i < |strings| ==> forall j :: 0 <= j < |strings[i]| ==> strings[i][j] == 's' || strings[i][j] == 'h'
    ensures |sorted| == |strings|
    ensures multiset(strings) == multiset(sorted)
    ensures forall i :: 0 <= i < |sorted| ==> |sorted[i]| > 0
    ensures forall i :: 0 <= i < |sorted| ==> forall j :: 0 <= j < |sorted[i]| ==> sorted[i][j] == 's' || sorted[i][j] == 'h'
    ensures IsSortedByRatio(sorted)
{
    sorted := [];
    for i := 0 to |strings| - 1
        invariant |sorted| == i
        invariant multiset(strings[..i]) == multiset(sorted)
        invariant forall j :: 0 <= j < |sorted| ==> |sorted[j]| > 0
        invariant forall j :: 0 <= j < |sorted| ==> forall k :: 0 <= k < |sorted[j]| ==> sorted[j][k] == 's' || sorted[j][k] == 'h'
        invariant IsSortedByRatio(sorted)
    {
        var newelement := strings[i];
        var pos := 0;
        while pos < |sorted| && StringRatio(sorted[pos]) <= StringRatio(newelement)
            invariant 0 <= pos <= |sorted|
            invariant forall j :: 0 <= j < |sorted| ==> |sorted[j]| > 0
            invariant forall k :: 0 <= k < pos ==> StringRatio(sorted[k]) <= StringRatio(newelement)
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
    var s := input[0];
    var n := 0;
    for i := 0 to |s| - 1
        invariant 0 <= i <= |s|
        invariant n >= 0
    {
        var d := s[i] as int - '0' as int;
        n := n * 10 + d;
    }
    assert n >= 1 && |input| >= n + 1;
    var strings := input[1..n+1];
    var sorted := SortByRatio(strings);
    var concatenated := "";
    for i := 0 to |sorted| - 1
        invariant 0 <= i <= |sorted|
        invariant forall j :: 0 <= j < |concatenated| ==> concatenated[j] == 's' || concatenated[j] == 'h'
    {
        concatenated := concatenated + sorted[i];
    }
    var index := 0;
    var s_count := 0;
    var res := 0;
    while index < |concatenated|
        invariant 0 <= index <= |concatenated|
        invariant s_count >= 0
        invariant res >= 0
    {
        if concatenated[index] == 's' {
            s_count := s_count + 1;
        } else if concatenated[index] == 'h' {
            res := res + s_count;
        }
        index := index + 1;
    }
    result := res;
}
// </vc-code>

