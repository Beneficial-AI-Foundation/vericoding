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
function splitLines(s: string): seq<string>
{
    if |s| == 0 then []
    else if s[|s|-1] == '\n' then splitLines(s[..|s|-1]) + [""]
    else [s]
}

function parseInt(s: string): int
    requires |s| > 0
    requires forall i :: 0 <= i < |s| ==> s[i] >= '0' && s[i] <= '9'
{
    if |s| == 1 then s[0] as int - '0' as int
    else if s[0] >= '0' && s[0] <= '9' then (s[0] as int - '0' as int) * pow(10, |s| - 1) + parseInt(s[1..])
    else 0
}

function pow(base: int, exponent: int): int
    decreases exponent
{
    if exponent <= 0 then 1
    else base * pow(base, exponent - 1)
}

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

lemma lemma4(s: string)
    ensures isValidPositiveInteger(s) ==> (|s| >= 1 && (forall i :: 0 <= i < |s| ==> s[i] >= '0' && s[i] <= '9') && (|s| == 1 || s[0] != '0'))
{
}

lemma lemma5(s: string)
    requires |s| >= 1
    requires forall i :: 0 <= i < |s| ==> s[i] >= '0' && s[i] <= '9'
    requires |s| == 1 || s[0] != '0'
    ensures isValidPositiveInteger(s)
{
}

lemma lemma6(s: string)
    ensures |splitLines(s)| > 0 ==> |splitLines(s)[0]| > 0
{
}

lemma lemma7(s: string)
    ensures |s| > 0 ==> forall i :: 0 <= i < |s| ==> s[i] >= '0' && s[i] <= '9'
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
    var n_str := lines[0];
    var n := 0;
    if |n_str| > 0 {
        assert forall i :: 0 <= i < |n_str| ==> n_str[i] >= '0' && n_str[i] <= '9' by {
            lemma7(n_str);
        }
        n := parseInt(n_str);
    }
    
    if n <= 0 {
        result := "NO\n";
        return;
    }
    
    var inputStrings := lines[1..n+1];
    
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
        var minString := current;
        
        var j := 0;
        while j < |current|
            invariant 0 <= j <= |current|
            invariant |minString| == |current|
            invariant forall k :: 0 <= k < j ==> 
                (current[k] == '?' ==> minString[k] == '0') &&
                (current[k] != '?' ==> minString[k] == current[k])
            invariant forall k :: j <= k < |current| ==> minString[k] == current[k]
        {
            if current[j] == '?' {
                minString := minString[..j] + "0" + minString[j+1..];
            }
            j := j + 1;
        }
        
        assert |minString| >= 1;
        assert forall k :: 0 <= k < |minString| ==> minString[k] >= '0' && minString[k] <= '9';
        assert |minString| == 1 || minString[0] != '0';
        
        if i == 0 {
            solution[i] := minString;
            assert isValidPositiveInteger(minString) by {
                lemma5(minString);
            }
        } else {
            var candidate := minString;
            var found := false;
            
            assert isValidPositiveInteger(solution[i-1]);
            assert isValidPositiveInteger(candidate);
            
            if isLexicographicallySmaller(solution[i-1], candidate) {
                solution[i] := candidate;
                found := true;
            }
            
            if !found {
                result := "NO\n";
                return;
            }
        }
        
        i := i + 1;
    }
    
    result := "YES\n";
}
// </vc-code>

