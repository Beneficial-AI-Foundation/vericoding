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
predicate IsValidInputAfterFirstLineSplit(lines: seq<string>, N: int, x: int) {
    |lines| >= 2 &&
    var secondLine := SplitBySpaceSpec(lines[1]);
    |secondLine| == N &&
    (forall i :: 0 <= i < N ==> ParseIntSpec(secondLine[i]) >= 0)
}

predicate IsValidFirstLine(firstLine: seq<string>) {
    |firstLine| >= 2 &&
    var N := ParseIntSpec(firstLine[0]);
    var x := ParseIntSpec(firstLine[1]);
    N >= 2 && x >= 0
}

lemma ValidInputImpliesValidFirstAndSecondLines(input: string)
    requires ValidInput(input)
    ensures var lines := SplitByNewlineSpec(input);
            var firstLine := SplitBySpaceSpec(lines[0]);
            IsValidFirstLine(firstLine) &&
            IsValidInputAfterFirstLineSplit(lines, ParseIntSpec(firstLine[0]), ParseIntSpec(firstLine[1]))
{
}

lemma SequenceOperationsValid(originalA: seq<int>, x: int, currentA: seq<int>, index: int, currentCount: int)
    requires |originalA| >= 2
    requires x >= 0
    requires 1 <= index <= |originalA|
    requires |currentA| == |originalA|
    requires currentCount >= 0
    requires forall i :: 0 <= i < |originalA| ==> originalA[i] >= 0
    requires forall i :: 0 <= i < |originalA| ==> currentA[i] >= 0
    ensures var newValue := if currentA[index] + currentA[index-1] > x then x - currentA[index-1] else currentA[index];
            var newA := currentA[index := newValue];
            forall i :: 0 <= i < |newA| ==> newA[i] >= 0
{
}

lemma AdditionalOpsNonNegative(currentA: seq<int>, index: int, x: int)
    requires |currentA| > index
    requires index >= 1
    requires x >= 0
    requires forall i :: 0 <= i < |currentA| ==> currentA[i] >= 0
    ensures var additionalOps := if currentA[index] + currentA[index-1] > x then currentA[index] + currentA[index-1] - x else 0;
            additionalOps >= 0
{
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
    var lines := SplitByNewlineSpec(input);
    var firstLine := SplitBySpaceSpec(lines[0]);
    var N := ParseIntSpec(firstLine[0]);
    var x := ParseIntSpec(firstLine[1]);
    var secondLine := SplitBySpaceSpec(lines[1]);
    
    var candyCounts := seq(N, i requires 0 <= i < N => ParseIntSpec(secondLine[i]));
    var totalOperations := 0;
    
    if candyCounts[0] > x {
        totalOperations := candyCounts[0] - x;
        candyCounts := candyCounts[0 := x];
    }
    
    var i: int := 1;
    while (i < N)
        invariant 1 <= i <= N
        invariant totalOperations >= 0
        invariant |candyCounts| == N
        invariant forall j :: 0 <= j < N ==> candyCounts[j] >= 0
    {
        if candyCounts[i] + candyCounts[i-1] > x {
            var diff := candyCounts[i] + candyCounts[i-1] - x;
            totalOperations := totalOperations + diff;
            candyCounts := candyCounts[i := candyCounts[i] - diff];
        }
        i := i + 1;
    }
    
    result := IntToString(totalOperations) + "\n";
}
// </vc-code>

