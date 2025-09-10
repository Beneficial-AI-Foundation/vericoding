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

// <vc-helpers>
function SplitByNewlineSpec(s: string): seq<string>
{
    Split(s, '\n')
}

function SplitBySpaceSpec(s: string): seq<string>
{
    Split(s, ' ')
}

function Split(s: seq<char>, d: char): seq<seq<char>>
    decreases |s|
{
    if |s| == 0 then []
    else
        var pos := FindIndexOf(s, d, 0);
        if pos == -1 then [s]
        else
            [s[..pos]] + Split(s[pos+1..], d)
}

function FindIndexOf(s: seq<char>, d: char, from: int): int
    requires 0 <= from <= |s|
    decreases |s| - from
{
    if from == |s| then -1
    else if s[from] == d then from
    else FindIndexOf(s, d, from + 1)
}

function IsDigit(c: char): bool
{
    '0' <= c && c <= '9'
}

function ParseIntSpec(s: string): int
    requires |s| > 0
    requires forall i :: 0 <= i < |s| ==> IsDigit(s[i])
    decreases |s|
{
    if |s| == 1 then
        s[0] - '0' as int
    else
        10 * ParseIntSpec(s[..|s|-1]) + (s[|s|-1] - '0') as int
}

function IntToString(n: int): string
    requires n >= 0
{
    if n == 0 then "0"
    else
        Digits(n)
}

function Digits(n: int): seq<char>
    requires n >= 0
    ensures |Digits(n)| > 0
    decreases n
{
    if n == 0 then []
    else
        var lowDigit := char((n % 10) + '0' as int);
        Digits(n / 10) + [lowDigit]
}
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (result: string)
    requires |input| > 0
    requires ValidInput(input)
    ensures |result| > 0
    ensures result == IntToString(MinimumCandiesNeeded(input)) + "\n"
// </vc-spec>
// <vc-code>
{
    var count := MinimumCandiesNeeded(input);
    result := IntToString(count) + "\n";
}
// </vc-code>

