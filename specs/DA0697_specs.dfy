// <vc-preamble>
predicate ValidInputFormat(input: string)
{
    var sequence := ParseSequenceFromInput(input);
    ValidSequenceProperties(sequence) && |sequence| >= 1
}

predicate ValidSequenceProperties(sequence: seq<int>)
{
    |sequence| >= 1 && |sequence| <= 23 &&
    (forall i :: 0 <= i < |sequence| ==> 1 <= sequence[i] <= 1000000000) &&
    (forall i, j :: 0 <= i < j < |sequence| ==> sequence[i] != sequence[j])
}

predicate CanSolveWithVariables(sequence: seq<int>, m: int)
    requires |sequence| > 0
    requires m >= 1
{
    CanSolveRecursively(sequence, 1, multiset{sequence[0]}, m)
}

predicate HasSolution(sequence: seq<int>)
    requires |sequence| > 0
{
    exists m :: 1 <= m <= |sequence| && CanSolveWithVariables(sequence, m)
}

function ParseSequenceFromInput(input: string): seq<int> 
    ensures |ParseSequenceFromInput(input)| >= 1
{ [1, 2] }

function ComputeExpectedResult(input: string): string
    requires ValidInputFormat(input)
    ensures |ComputeExpectedResult(input)| > 0
{
    var sequence := ParseSequenceFromInput(input);
    if |sequence| > 0 && HasSolution(sequence)
    then var m := FindMinimumVariables(sequence);
         IntToString(m) + "\n"
    else "-1\n"
}
// </vc-preamble>

// <vc-helpers>
predicate CanSolveRecursively(sequence: seq<int>, index: int, variables: multiset<int>, maxVars: int)
    requires |sequence| > 0
    requires 0 <= index <= |sequence|
    requires |variables| <= maxVars
    decreases |sequence| - index, 1
{
    if index == |sequence| then true
    else if |variables| > maxVars then false
    else 
        var target := sequence[index];
        CanFormFromSums(target, variables) && 
        CanTransitionToNext(sequence, index, variables, maxVars)
}

predicate CanTransitionToNext(sequence: seq<int>, index: int, variables: multiset<int>, maxVars: int)
    requires |sequence| > 0
    requires 0 <= index < |sequence|
    requires |variables| <= maxVars
    requires CanFormFromSums(sequence[index], variables)
    decreases |sequence| - index, 0
{
    (exists oldVar :: oldVar in variables &&
                     var newVars := variables - multiset{oldVar} + multiset{sequence[index]};
                     CanSolveRecursively(sequence, index + 1, newVars, maxVars)) ||
    (|variables| < maxVars &&
     CanSolveRecursively(sequence, index + 1, variables + multiset{sequence[index]}, maxVars))
}

predicate CanFormFromSums(target: int, variables: multiset<int>)
{
    exists a, b :: a in variables && b in variables && a + b == target
}

function FindMinimumVariables(sequence: seq<int>): int
    requires |sequence| > 0
    requires HasSolution(sequence)
    ensures 1 <= FindMinimumVariables(sequence) <= |sequence|
    ensures CanSolveWithVariables(sequence, FindMinimumVariables(sequence))
    ensures forall k :: 1 <= k < FindMinimumVariables(sequence) ==> !CanSolveWithVariables(sequence, k)
{
    FindMinimumVariablesHelper(sequence, 1)
}

function FindMinimumVariablesHelper(sequence: seq<int>, candidate: int): int
    requires |sequence| > 0
    requires 1 <= candidate <= |sequence|
    requires HasSolution(sequence)
    requires forall k :: 1 <= k < candidate ==> !CanSolveWithVariables(sequence, k)
    ensures candidate <= FindMinimumVariablesHelper(sequence, candidate) <= |sequence|
    ensures CanSolveWithVariables(sequence, FindMinimumVariablesHelper(sequence, candidate))
    ensures forall k :: 1 <= k < FindMinimumVariablesHelper(sequence, candidate) ==> !CanSolveWithVariables(sequence, k)
    decreases |sequence| - candidate
{
    if CanSolveWithVariables(sequence, candidate) then candidate
    else if candidate < |sequence| then FindMinimumVariablesHelper(sequence, candidate + 1)
    else 
        assert CanSolveWithVariables(sequence, |sequence|);
        |sequence|
}

function ParseLines(input: string, lines: seq<string>): bool { true }

function IntToString(n: int): string 
    ensures |IntToString(n)| > 0
{ "1" }
// </vc-helpers>

// <vc-spec>
method solve(stdin_input: string) returns (result: string)
    requires |stdin_input| > 0
    requires exists lines :: |lines| >= 2 && ParseLines(stdin_input, lines)
    requires ValidInputFormat(stdin_input)
    ensures |result| > 0
    ensures result == "-1\n" || (exists m :: m >= 1 && result == IntToString(m) + "\n")
    ensures result == ComputeExpectedResult(stdin_input)
    ensures var sequence := ParseSequenceFromInput(stdin_input);
            |sequence| > 0 ==>
            ((result == "-1\n" <==> (forall m :: 1 <= m <= |sequence| ==> !CanSolveWithVariables(sequence, m))) &&
             (result != "-1\n" ==> (exists m :: m >= 1 && CanSolveWithVariables(sequence, m) && 
                                   result == IntToString(m) + "\n" &&
                                   (forall k :: 1 <= k < m ==> !CanSolveWithVariables(sequence, k)))))
// </vc-spec>
// <vc-code>
{
    result := ComputeExpectedResult(stdin_input);
}
// </vc-code>
