Given N boxes in a row with a_i candies in the i-th box, find the minimum number of candies 
to eat such that every pair of adjacent boxes contains at most x candies in total.
Operation: Choose any box with at least one candy and eat one candy from it.
Objective: For all i from 1 to N-1, ensure a_i + a_{i+1} ≤ x.

predicate ValidInput(input: string)
{
    var lines := SplitByNewlineSpec(input);
    |lines| >= 2 &&
    var firstLine := SplitBySpaceSpec(lines[0]);
    |firstLine| >= 2 &&
    var N := ParseIntSpec(firstLine[0]);
    var x := ParseIntSpec(firstLine[1]);
    N >= 2 && x >= 0 &&
    var secondLine := SplitBySpaceSpec(lines[1]);
    |secondLine| == N &&
    (forall i :: 0 <= i < N ==> ParseIntSpec(secondLine[i]) >= 0)
}

function MinimumCandiesNeeded(input: string): int
    requires ValidInput(input)
    ensures MinimumCandiesNeeded(input) >= 0
{
    var lines := SplitByNewlineSpec(input);
    var firstLine := SplitBySpaceSpec(lines[0]);
    var N := ParseIntSpec(firstLine[0]);
    var x := ParseIntSpec(firstLine[1]);
    var secondLine := SplitBySpaceSpec(lines[1]);
    var A := seq(N, i requires 0 <= i < N => ParseIntSpec(secondLine[i]));
    ComputeMinimumOperations(A, x)
}

function ComputeMinimumOperations(A: seq<int>, x: int): int
    requires |A| >= 2
    requires x >= 0
    requires forall i :: 0 <= i < |A| ==> A[i] >= 0
    ensures ComputeMinimumOperations(A, x) >= 0
{
    var A0 := if A[0] > x then x else A[0];
    var cnt0 := if A[0] > x then A[0] - x else 0;
    ComputeOperationsFromIndex(A, x, 1, [A0] + A[1..], cnt0)
}

function ComputeOperationsFromIndex(originalA: seq<int>, x: int, index: int, currentA: seq<int>, currentCount: int): int
    requires |originalA| >= 2
    requires x >= 0
    requires 1 <= index <= |originalA|
    requires |currentA| == |originalA|
    requires currentCount >= 0
    requires forall i :: 0 <= i < |originalA| ==> originalA[i] >= 0
    ensures ComputeOperationsFromIndex(originalA, x, index, currentA, currentCount) >= currentCount
    decreases |originalA| - index
{
    if index >= |originalA| then currentCount
    else
        var newValue := if currentA[index] + currentA[index-1] > x then x - currentA[index-1] else currentA[index];
        var additionalOps := if currentA[index] + currentA[index-1] > x then currentA[index] + currentA[index-1] - x else 0;
        var newA := currentA[index := newValue];
        ComputeOperationsFromIndex(originalA, x, index + 1, newA, currentCount + additionalOps)
}

function IntToString(n: int): string
{
    if n == 0 then "0"
    else if n < 0 then "-" + IntToStringHelper(-n, "")
    else IntToStringHelper(n, "")
}

function IntToStringHelper(n: int, acc: string): string
    requires n >= 0
    decreases n
{
    if n == 0 then acc
    else IntToStringHelper(n / 10, [(n % 10 + 48) as char] + acc)
}

function SplitByNewlineSpec(s: string): seq<string>
{
    SplitByNewlineImpl(s, 0, "", [])
}

function SplitByNewlineImpl(s: string, index: int, current: string, acc: seq<string>): seq<string>
    requires 0 <= index <= |s|
    decreases |s| - index
{
    if index >= |s| then
        if current == "" then acc else acc + [current]
    else if s[index] == '\n' then
        SplitByNewlineImpl(s, index + 1, "", acc + [current])
    else
        SplitByNewlineImpl(s, index + 1, current + [s[index]], acc)
}

function SplitBySpaceSpec(s: string): seq<string>
{
    SplitBySpaceImpl(s, 0, "", [])
}

function SplitBySpaceImpl(s: string, index: int, current: string, acc: seq<string>): seq<string>
    requires 0 <= index <= |s|
    decreases |s| - index
{
    if index >= |s| then
        if current == "" then acc else acc + [current]
    else if s[index] == ' ' then
        if current == "" then
            SplitBySpaceImpl(s, index + 1, "", acc)
        else
            SplitBySpaceImpl(s, index + 1, "", acc + [current])
    else
        SplitBySpaceImpl(s, index + 1, current + [s[index]], acc)
}

function ParseIntSpec(s: string): int
{
    ParseIntImpl(s, 0, 0)
}

function ParseIntImpl(s: string, index: int, acc: int): int
    requires 0 <= index <= |s|
    decreases |s| - index
{
    if index >= |s| then acc
    else if '0' <= s[index] <= '9' then
        ParseIntImpl(s, index + 1, acc * 10 + (s[index] as int - '0' as int))
    else
        ParseIntImpl(s, index + 1, acc)
}

method SplitByNewline(s: string) returns (lines: seq<string>)
    ensures lines == SplitByNewlineSpec(s)
{
    lines := SplitByNewlineImpl(s, 0, "", []);
}

method SplitBySpace(s: string) returns (words: seq<string>)
    ensures words == SplitBySpaceSpec(s)
{
    words := SplitBySpaceImpl(s, 0, "", []);
}

method ParseInt(s: string) returns (n: int)
    ensures n == ParseIntSpec(s)
{
    n := ParseIntImpl(s, 0, 0);
}

method solve(input: string) returns (result: string)
    requires |input| > 0
    requires ValidInput(input)
    ensures |result| > 0
    ensures result == IntToString(MinimumCandiesNeeded(input)) + "\n"
{
    var lines := SplitByNewline(input);
    var firstLine := SplitBySpace(lines[0]);
    var N := ParseInt(firstLine[0]);
    var x := ParseInt(firstLine[1]);

    var secondLine := SplitBySpace(lines[1]);
    var A := new int[N];
    for i := 0 to N {
        A[i] := ParseInt(secondLine[i]);
    }

    var cnt := MinimumCandiesNeeded(input);
    result := IntToString(cnt) + "\n";
}
