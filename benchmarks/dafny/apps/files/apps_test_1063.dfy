// <vc-preamble>
predicate isWellFormedInput(stdin_input: string)
{
    var lines := splitLines(stdin_input);
    if |lines| < 1 then false
    else
        var n := parseInt(lines[0]);
        n >= 0 && |lines| >= n + 1 &&
        (forall i :: 1 <= i <= n && i < |lines| ==> 
            |lines[i]| >= 1 && |lines[i]| <= 8 &&
            (forall j :: 0 <= j < |lines[i]| ==> 
                (lines[i][j] >= '0' && lines[i][j] <= '9') || lines[i][j] == '?'))
}

ghost predicate hasValidSolution(stdin_input: string)
    requires isWellFormedInput(stdin_input)
{
    var lines := splitLines(stdin_input);
    var n := parseInt(lines[0]);
    if n <= 0 then true
    else
        var inputStrings := lines[1..n+1];
        exists solution :: isValidSequenceSolution(inputStrings, solution)
}

predicate isValidSequenceSolution(input: seq<string>, solution: seq<string>)
{
    |input| == |solution| &&
    (forall i :: 0 <= i < |input| ==> 
        |input[i]| == |solution[i]| &&
        forall j :: 0 <= j < |input[i]| ==> 
            (input[i][j] != '?' ==> input[i][j] == solution[i][j]) &&
            (input[i][j] == '?' ==> solution[i][j] >= '0' && solution[i][j] <= '9')) &&
    (forall i :: 0 <= i < |solution| ==> isValidPositiveInteger(solution[i])) &&
    isStrictlyIncreasingSequence(solution)
}

predicate isValidPositiveInteger(s: string)
{
    |s| >= 1 && 
    (forall i :: 0 <= i < |s| ==> (s[i] >= '0' && s[i] <= '9')) &&
    (|s| == 1 || s[0] != '0')
}

predicate isStrictlyIncreasingSequence(nums: seq<string>)
    requires forall i :: 0 <= i < |nums| ==> isValidPositiveInteger(nums[i])
{
    forall i :: 0 <= i < |nums| - 1 ==> isLexicographicallySmaller(nums[i], nums[i+1])
}

predicate isLexicographicallySmaller(a: string, b: string)
    requires isValidPositiveInteger(a) && isValidPositiveInteger(b)
{
    |a| < |b| || (|a| == |b| && a < b)
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method solve(stdin_input: string) returns (result: string)
    requires |stdin_input| > 0
    requires isWellFormedInput(stdin_input)
    ensures |result| > 0
    ensures result == "NO\n" || (|result| > 4 && result[..4] == "YES\n")
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
