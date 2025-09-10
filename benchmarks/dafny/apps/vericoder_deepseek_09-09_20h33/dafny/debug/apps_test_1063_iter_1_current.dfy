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

// <vc-helpers>
lemma lemma1(a: string, b: string, i: int, j: int)
    requires 0 <= i < |a|
    requires 0 <= j < |b|
    requires a[i] >= '0' && a[i] <= '9'
    requires b[j] >= '0' && b[j] <= '9'
    ensures (|a| < |b|) ==> (a[..i] == b[..j] && a[i] < b[j]) ==> a < b
{
}

lemma lemma2(a: string, b: string)
    requires |a| <= |b|
    requires a != b
    requires a < b
    ensures isLexicographicallySmaller(a, b)
{
}

lemma lemma3(a: string, b: string)
    requires |a| < |b|
    ensures isLexicographicallySmaller(a, b)
{
}
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
    var lines := splitLines(stdin_input);
    var n := parseInt(lines[0]);
    
    if n <= 0 {
        result := "NO\n";
        return;
    }
    
    var inputStrings := lines[1..n+1];
    ghost var allSolutions := [];
    var lastIndex := -1;
    
    var solution := new string[n];
    var i := 0;
    
    while i < n
        invariant 0 <= i <= n
        invariant forall k :: 0 <= k < i ==> |inputStrings[k]| == |solution[k]|
        invariant forall k :: 0 <= k < i ==> 
            forall j :: 0 <= j < |inputStrings[k]| ==>
                (inputStrings[k][j] != '?' ==> inputStrings[k][j] == solution[k][j]) &&
                (inputStrings[k][j] == '?' ==> solution[k][j] >= '0' && solution[k][j] <= '9')
        invariant forall k :: 0 <= k < i ==> isValidPositiveInteger(solution[k])
        invariant forall k :: 0 <= k < i - 1 ==> isLexicographicallySmaller(solution[k], solution[k+1])
    {
        var current := inputStrings[i];
        var minString := "";
        var maxString := current;
        
        var j := 0;
        while j < |current|
            invariant 0 <= j <= |current|
            invariant minString == current
        {
            if current[j] == '?' {
                minString := minString[..j] + "0" + minString[j+1..];
                maxString := maxString[..j] + "9" + maxString[j+1..];
            } else {
                minString := minString[..j] + current[j..j+1] + minString[j+1..];
                maxString := maxString[..j] + current[j..j+1] + maxString[j+1..];
            }
            j := j + 1;
        }
        
        if i == 0 {
            solution[i] := minString;
        } else {
            solution[i] := minString;
            if !isLexicographicallySmaller(solution[i-1], solution[i]) {
                result := "NO\n";
                return;
            }
        }
        
        i := i + 1;
    }
    
    result := "YES\n";
}
// </vc-code>

