This task implements a stone pile transformation problem. Given n piles of stones with initial and final counts, determine if the transformation is possible using two operations: (1) remove one stone from any pile, or (2) move one stone from one pile to another. The solution should output "Yes" if the transformation is possible, "No" otherwise.

The key insight is that the total number of stones can only decrease or stay the same (since we can remove stones but not add them), so the transformation is possible if and only if the initial sum is greater than or equal to the final sum.

// ======= TASK =======
// Given n piles of stones with initial and final counts, determine if transformation
// is possible using operations: (1) remove one stone from any pile, (2) move one
// stone from one pile to another. Output "Yes" if possible, "No" otherwise.

// ======= SPEC REQUIREMENTS =======
function SumSeq(arr: seq<int>): int
{
    if |arr| == 0 then 0 else arr[0] + SumSeq(arr[1..])
}

function SplitLinesFunc(s: string): seq<string>
{
    SplitLinesHelper(s, 0, "", [])
}

function SplitLinesHelper(s: string, i: int, current: string, lines: seq<string>): seq<string>
    requires 0 <= i <= |s|
    decreases |s| - i
{
    if i >= |s| then
        if |current| > 0 then lines + [current] else lines
    else if s[i] == '\n' then
        SplitLinesHelper(s, i + 1, "", lines + [current])
    else
        SplitLinesHelper(s, i + 1, current + [s[i]], lines)
}

function ParseIntFunc(s: string): int
{
    ParseIntHelper(s, 0, 0)
}

function ParseIntHelper(s: string, i: int, acc: int): int
    requires 0 <= i <= |s|
    decreases |s| - i
{
    if i >= |s| then acc
    else if s[i] >= '0' && s[i] <= '9' then
        ParseIntHelper(s, i + 1, acc * 10 + (s[i] as int - '0' as int))
    else
        ParseIntHelper(s, i + 1, acc)
}

function ParseIntArrayFunc(s: string): seq<int>
{
    ParseIntArrayHelper(s, 0, "", [])
}

function ParseIntArrayHelper(s: string, i: int, current: string, arr: seq<int>): seq<int>
    requires 0 <= i <= |s|
    decreases |s| - i
{
    if i >= |s| then
        if |current| > 0 then arr + [ParseIntFunc(current)] else arr
    else if s[i] == ' ' then
        if |current| > 0 then
            ParseIntArrayHelper(s, i + 1, "", arr + [ParseIntFunc(current)])
        else
            ParseIntArrayHelper(s, i + 1, "", arr)
    else
        ParseIntArrayHelper(s, i + 1, current + [s[i]], arr)
}

predicate ValidInput(input: string)
{
    var lines := SplitLinesFunc(input);
    |lines| >= 3 && 
    ParseIntFunc(lines[0]) > 0 && 
    |ParseIntArrayFunc(lines[1])| == ParseIntFunc(lines[0]) && 
    |ParseIntArrayFunc(lines[2])| == ParseIntFunc(lines[0])
}

predicate TransformationPossible(input: string)
    requires ValidInput(input)
{
    var lines := SplitLinesFunc(input);
    var initialStones := ParseIntArrayFunc(lines[1]);
    var finalStones := ParseIntArrayFunc(lines[2]);
    SumSeq(initialStones) >= SumSeq(finalStones)
}

// ======= HELPERS =======
lemma SumSeqAppendLemma(arr: seq<int>, x: int)
    ensures SumSeq(arr + [x]) == SumSeq(arr) + x
{
    if |arr| == 0 {
        assert arr + [x] == [x];
        assert SumSeq([x]) == x + SumSeq([]) == x + 0 == x;
        assert SumSeq(arr) + x == 0 + x == x;
    } else {
        assert arr == [arr[0]] + arr[1..];
        assert arr + [x] == [arr[0]] + (arr[1..] + [x]);
        SumSeqAppendLemma(arr[1..], x);
        assert SumSeq(arr[1..] + [x]) == SumSeq(arr[1..]) + x;
        assert SumSeq(arr + [x]) == arr[0] + SumSeq(arr[1..] + [x]) == arr[0] + SumSeq(arr[1..]) + x == SumSeq(arr) + x;
    }
}

method SplitLines(s: string) returns (lines: seq<string>)
    requires |s| >= 0
    ensures |lines| >= 0
    ensures lines == SplitLinesFunc(s)
    ensures forall i :: 0 <= i < |lines| ==> '\n' !in lines[i]
{
    lines := [];
    var current := "";
    var i := 0;

    while i < |s|
        invariant 0 <= i <= |s|
        invariant SplitLinesHelper(s, i, current, lines) == SplitLinesFunc(s)
        invariant forall j :: 0 <= j < |lines| ==> '\n' !in lines[j]
        invariant '\n' !in current
    {
        if s[i] == '\n' {
            lines := lines + [current];
            current := "";
        } else {
            current := current + [s[i]];
        }
        i := i + 1;
    }

    if |current| > 0 {
        lines := lines + [current];
    }
}

method ParseInt(s: string) returns (n: int)
    requires |s| >= 0
    ensures n >= 0
    ensures n == ParseIntFunc(s)
{
    n := 0;
    var i := 0;

    while i < |s|
        invariant 0 <= i <= |s|
        invariant n >= 0
        invariant ParseIntHelper(s, i, n) == ParseIntFunc(s)
    {
        if s[i] >= '0' && s[i] <= '9' {
            n := n * 10 + (s[i] as int - '0' as int);
        }
        i := i + 1;
    }
}

method ParseIntArray(s: string) returns (arr: seq<int>)
    requires |s| >= 0
    ensures |arr| >= 0
    ensures arr == ParseIntArrayFunc(s)
    ensures forall i :: 0 <= i < |arr| ==> arr[i] >= 0
{
    arr := [];
    var current := "";
    var i := 0;

    while i < |s|
        invariant 0 <= i <= |s|
        invariant ParseIntArrayHelper(s, i, current, arr) == ParseIntArrayFunc(s)
        invariant forall j :: 0 <= j < |arr| ==> arr[j] >= 0
    {
        if s[i] == ' ' {
            if |current| > 0 {
                var tmpCall1 := ParseInt(current);
                arr := arr + [tmpCall1];
                current := "";
            }
        } else {
            current := current + [s[i]];
        }
        i := i + 1;
    }

    if |current| > 0 {
        var tmpCall2 := ParseInt(current);
        arr := arr + [tmpCall2];
    }
}

method SumArray(arr: seq<int>) returns (sum: int)
    requires |arr| >= 0
    requires forall i :: 0 <= i < |arr| ==> arr[i] >= 0
    ensures sum >= 0
    ensures sum == SumSeq(arr)
{
    sum := 0;
    var i := 0;

    while i < |arr|
        invariant 0 <= i <= |arr|
        invariant sum == SumSeq(arr[..i])
        invariant sum >= 0
    {
        SumSeqAppendLemma(arr[..i], arr[i]);
        assert arr[..i] + [arr[i]] == arr[..i+1];
        sum := sum + arr[i];
        i := i + 1;
    }

    assert i == |arr|;
    assert arr[..i] == arr;
}

// ======= MAIN METHOD =======
method solve(input: string) returns (output: string)
    requires |input| > 0
    ensures output == "Yes" || output == "No"
    ensures ValidInput(input) ==> (output == "Yes" <==> TransformationPossible(input))
    ensures !ValidInput(input) ==> output == "No"
{
    var lines := SplitLines(input);
    if |lines| < 3 {
        return "No";
    }

    var n := ParseInt(lines[0]);
    if n <= 0 {
        return "No";
    }

    var initialStones := ParseIntArray(lines[1]);
    var finalStones := ParseIntArray(lines[2]);

    if |initialStones| != n || |finalStones| != n {
        return "No";
    }

    var initialSum := SumArray(initialStones);
    var finalSum := SumArray(finalStones);

    if initialSum >= finalSum {
        output := "Yes";
    } else {
        output := "No";
    }
}
