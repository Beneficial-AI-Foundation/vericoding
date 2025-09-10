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

function parseInt(s: string): int

lemma parseIntProperties(s: string)
    ensures parseInt(s) >= 0

method fillQuestionMarks(pattern: string) returns (filled: string)
    requires |pattern| >= 1 && |pattern| <= 8
    requires forall j :: 0 <= j < |pattern| ==> 
        (pattern[j] >= '0' && pattern[j] <= '9') || pattern[j] == '?'
    ensures |filled| == |pattern|
    ensures forall j :: 0 <= j < |filled| ==> filled[j] >= '0' && filled[j] <= '9'
    ensures forall j :: 0 <= j < |pattern| ==> 
        (pattern[j] != '?' ==> filled[j] == pattern[j])
    ensures isValidPositiveInteger(filled)
{
    filled := "";
    var i := 0;
    while i < |pattern|
        invariant 0 <= i <= |pattern|
        invariant |filled| == i
        invariant forall j :: 0 <= j < i ==> filled[j] >= '0' && filled[j] <= '9'
        invariant forall j :: 0 <= j < i ==> 
            (pattern[j] != '?' ==> filled[j] == pattern[j])
        invariant i > 0 ==> (i == 1 || filled[0] != '0')
    {
        if pattern[i] == '?' {
            if i == 0 && |pattern| > 1 {
                filled := filled + "1";
            } else if i == 0 && |pattern| == 1 {
                filled := filled + "1";
            } else {
                filled := filled + "0";
            }
        } else {
            filled := filled + [pattern[i]];
        }
        i := i + 1;
    }
}

method tryIncrementString(s: string) returns (result: string, success: bool)
    requires isValidPositiveInteger(s)
    ensures success ==> isValidPositiveInteger(result) && 
            isLexicographicallySmaller(s, result)
    ensures !success ==> result == ""
{
    var carry := 1;
    var i := |s| - 1;
    var digits := s;
    var mutableDigits := [];
    
    // Convert to mutable array
    var j := 0;
    while j < |s|
        invariant 0 <= j <= |s|
        invariant |mutableDigits| == j
        invariant forall k :: 0 <= k < j ==> mutableDigits[k] == s[k]
    {
        mutableDigits := mutableDigits + [s[j]];
        j := j + 1;
    }
    
    // Add 1 to the number
    while i >= 0 && carry == 1
        invariant -1 <= i < |s|
        invariant carry == 0 || carry == 1
        invariant |mutableDigits| == |s|
    {
        var digit := (mutableDigits[i] as int) - ('0' as int) + carry;
        if digit == 10 {
            mutableDigits := mutableDigits[..i] + ['0'] + mutableDigits[i+1..];
            carry := 1;
        } else {
            var newDigit := ('0' as int) + digit;
            mutableDigits := mutableDigits[..i] + [newDigit as char] + mutableDigits[i+1..];
            carry := 0;
        }
        i := i - 1;
    }
    
    if carry == 1 {
        // Need to add a digit
        result := "1";
        j := 0;
        while j < |mutableDigits|
            invariant 0 <= j <= |mutableDigits|
            invariant |result| == 1 + j
        {
            result := result + [mutableDigits[j]];
            j := j + 1;
        }
        success := true;
    } else {
        result := "";
        j := 0;
        while j < |mutableDigits|
            invariant 0 <= j <= |mutableDigits|
            invariant |result| == j
        {
            result := result + [mutableDigits[j]];
            j := j + 1;
        }
        success := true;
    }
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
    parseIntProperties(lines[0]);
    var n := parseInt(lines[0]);
    
    if n <= 0 {
        return "YES\n";
    }
    
    var inputStrings := lines[1..n+1];
    var solution := [];
    var i := 0;
    var lastNum := "";
    
    while i < |inputStrings|
        invariant 0 <= i <= |inputStrings|
        invariant |solution| == i
        invariant forall j :: 0 <= j < i ==> |solution[j]| == |inputStrings[j]|
        invariant forall j :: 0 <= j < i ==> isValidPositiveInteger(solution[j])
        invariant forall j :: 0 <= j < i ==> 
            forall k :: 0 <= k < |inputStrings[j]| ==>
                (inputStrings[j][k] != '?' ==> solution[j][k] == inputStrings[j][k])
        invariant i > 0 ==> lastNum == solution[i-1] && isValidPositiveInteger(lastNum)
        invariant forall j :: 0 <= j < i - 1 ==> 
            isLexicographicallySmaller(solution[j], solution[j+1])
    {
        var current := fillQuestionMarks(inputStrings[i]);
        
        if i == 0 {
            solution := solution + [current];
            lastNum := current;
        } else {
            // Check if current is greater than lastNum
            if isLexicographicallySmaller(lastNum, current) {
                solution := solution + [current];
                lastNum := current;
            } else {
                // Try to find a valid number by incrementing lastNum
                var next, success := tryIncrementString(lastNum);
                if !success || next == "" {
                    return "NO\n";
                }
                
                // Check if next matches the pattern
                if |next| != |inputStrings[i]| {
                    return "NO\n";
                }
                
                var matches := true;
                var j := 0;
                while j < |inputStrings[i]|
                    invariant 0 <= j <= |inputStrings[i]|
                    invariant matches ==> forall k :: 0 <= k < j ==>
                        (inputStrings[i][k] != '?' ==> inputStrings[i][k] == next[k])
                {
                    if inputStrings[i][j] != '?' && inputStrings[i][j] != next[j] {
                        matches := false;
                    }
                    j := j + 1;
                }
                
                if !matches {
                    return "NO\n";
                }
                
                solution := solution + [next];
                lastNum := next;
            }
        }
        i := i + 1;
    }
    
    result := "YES\n";
    i := 0;
    while i < |solution|
        invariant 0 <= i <= |solution|
    {
        result := result + solution[i] + "\n";
        i := i + 1;
    }
}
// </vc-code>

