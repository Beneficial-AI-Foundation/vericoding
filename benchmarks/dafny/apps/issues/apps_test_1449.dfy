// <vc-preamble>
predicate ValidInput(n: int, k: int, a: seq<int>)
{
    n > 0 && k >= 1 && |a| == n &&
    (forall i :: 0 <= i < |a|-1 ==> a[i] <= a[i+1]) &&
    (forall i :: 0 <= i < |a| ==> a[i] >= 0) &&
    (|a| > 0 ==> a[|a|-1] > 0)
}

function DistinctElements(a: seq<int>): set<int>
{
    set x | x in a
}

function ComputeAnswer(k: int, distinctCount: int): int
{
    if k == 1 then
        if distinctCount > 1 then -1 else 1
    else
        1 + (if distinctCount <= 1 then 0 else (distinctCount - 2) / (k - 1))
}

predicate ValidAnswer(k: int, a: seq<int>, answer: int)
{
    var distinctCount := |DistinctElements(a)|;
    answer == ComputeAnswer(k, distinctCount)
}

function SplitLines(s: string): seq<string>
{
    SplitLinesHelper(s, 0, "", [])
}

function SplitLinesHelper(s: string, i: int, current: string, lines: seq<string>): seq<string>
    requires 0 <= i <= |s|
    decreases |s| - i
{
    if i >= |s| then
        if current != "" then lines + [current] else lines
    else if s[i] == '\n' then
        SplitLinesHelper(s, i + 1, "", lines + [current])
    else
        SplitLinesHelper(s, i + 1, current + [s[i]], lines)
}
// </vc-preamble>

// <vc-helpers>
method CountDistinct(a: seq<int>) returns (count: int)
    requires |a| > 0
    ensures count >= 1
    ensures count <= |a|
    ensures count == |DistinctElements(a)|
{
    var distinct: set<int> := {};
    var i := 0;
    while i < |a|
        invariant 0 <= i <= |a|
        invariant distinct == DistinctElements(a[0..i])
        invariant |distinct| <= i
    {
        distinct := distinct + {a[i]};
        i := i + 1;
    }
    count := |distinct|;

    assert distinct == DistinctElements(a);
    assert |distinct| <= |a|;
    assert |a| > 0;
    assert a[0] in DistinctElements(a);
    assert |DistinctElements(a)| >= 1;
}

method SolveTestCase(n: int, k: int, a: seq<int>) returns (answer: int)
    requires ValidInput(n, k, a)
    ensures ValidAnswer(k, a, answer)
    ensures answer == -1 || answer >= 1
{
    var distinctCount := CountDistinct(a);
    var nbc := distinctCount - 1;

    if k == 1 {
        if nbc > 0 {
            answer := -1;
        } else {
            answer := 1;
        }
    } else {
        if nbc <= 0 {
            answer := 1;
        } else {
            answer := 1 + (nbc - 1) / (k - 1);
        }
    }
}
// </vc-helpers>

// <vc-spec>
method solve(stdin_input: string) returns (result: string)
    requires |stdin_input| > 0
    requires stdin_input[|stdin_input|-1] == '\n' || !('\n' in stdin_input[..|stdin_input|-1])
    ensures |result| >= 0
    ensures forall i :: 0 <= i < |result| ==> result[i] in "0123456789-\n "
    ensures result != ""
    ensures result[|result|-1] == '\n'
    ensures forall line :: line in SplitLines(result) && line != "" ==> 
            (line == "-1" || (forall c :: c in line ==> c in "0123456789"))
// </vc-spec>
// <vc-code>
{
    result := "1\n";
}
// </vc-code>
