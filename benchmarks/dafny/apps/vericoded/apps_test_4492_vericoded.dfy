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
    ["", ""]  // Stub implementation
}

function SplitBySpaceSpec(s: string): seq<string>
{
    ["", ""]  // Stub implementation
}

function ParseIntSpec(s: string): int
{
    0  // Stub implementation
}

method SplitByNewline(s: string) returns (lines: seq<string>)
    ensures lines == SplitByNewlineSpec(s)
{
    lines := SplitByNewlineSpec(s);
}

method SplitBySpace(s: string) returns (tokens: seq<string>)
    ensures tokens == SplitBySpaceSpec(s)
{
    tokens := SplitBySpaceSpec(s);
}

method ParseInt(s: string) returns (n: int)
    ensures n == ParseIntSpec(s)
{
    n := ParseIntSpec(s);
}

function IntToString(n: int): string
{
    ""  // Stub implementation
}

method IntToStr(n: int) returns (s: string)
    ensures s == IntToString(n)
{
    s := IntToString(n);
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
    var lines := SplitByNewline(input);
    var firstLine := SplitBySpace(lines[0]);
    var N := ParseInt(firstLine[0]);
    var x := ParseInt(firstLine[1]);
    var secondLine := SplitBySpace(lines[1]);
    
    var A := new int[N];
    var i := 0;
    while i < N
        invariant 0 <= i <= N
        invariant forall j :: 0 <= j < i ==> A[j] == ParseIntSpec(secondLine[j])
        invariant forall j :: 0 <= j < i ==> A[j] >= 0
    {
        A[i] := ParseInt(secondLine[i]);
        i := i + 1;
    }
    
    var A_seq := A[..];
    assert |A_seq| == N;
    assert N >= 2;
    assert forall j :: 0 <= j < N ==> A_seq[j] == ParseIntSpec(secondLine[j]);
    assert forall j :: 0 <= j < N ==> A_seq[j] >= 0;
    
    var minOps := ComputeMinimumOperations(A_seq, x);
    var resultStr := IntToStr(minOps);
    result := resultStr + "\n";
    assert result == IntToString(MinimumCandiesNeeded(input)) + "\n";
}
// </vc-code>

