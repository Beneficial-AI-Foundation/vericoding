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
function replaceWildcards(s: string, digits: seq<char>): string
    requires |digits| == count_wildcards(s)
    requires forall i :: 0 <= i < |digits| ==> digits[i] >= '0' && digits[i] <= '9'
{
    replaceWildcardsHelper(s, digits, 0, 0)
}

function replaceWildcardsHelper(s: string, digits: seq<char>, pos: int, digitIndex: int): string
    requires 0 <= pos <= |s|
    requires 0 <= digitIndex <= |digits|
    requires digitIndex == count_wildcards_in_range(s, 0, pos)
    requires forall i :: 0 <= i < |digits| ==> digits[i] >= '0' && digits[i] <= '9'
    decreases |s| - pos
{
    if pos == |s| then ""
    else if s[pos] == '?' then
        [digits[digitIndex]] + replaceWildcardsHelper(s, digits, pos + 1, digitIndex + 1)
    else
        [s[pos]] + replaceWildcardsHelper(s, digits, pos + 1, digitIndex)
}

function count_wildcards(s: string): int
{
    count_wildcards_in_range(s, 0, |s|)
}

function count_wildcards_in_range(s: string, start: int, end: int): int
    requires 0 <= start <= end <= |s|
    decreases end - start
{
    if start == end then 0
    else if s[start] == '?' then 1 + count_wildcards_in_range(s, start + 1, end)
    else count_wildcards_in_range(s, start + 1, end)
}

method tryFindSolution(input: seq<string>) returns (success: bool, solution: seq<string>)
    requires forall i :: 0 <= i < |input| ==> 
        |input[i]| >= 1 && |input[i]| <= 8 &&
        (forall j :: 0 <= j < |input[i]| ==> 
            (input[i][j] >= '0' && input[i][j] <= '9') || input[i][j] == '?')
    ensures success ==> isValidSequenceSolution(input, solution)
    ensures !success ==> solution == []
{
    if |input| == 0 {
        return true, [];
    }
    
    solution := [];
    var current := "1";
    
    for i := 0 to |input|
        invariant 0 <= i <= |input|
        invariant |solution| == i
        invariant i > 0 ==> isValidPositiveInteger(current)
        invariant forall k :: 0 <= k < i ==> 
            |input[k]| == |solution[k]| &&
            (forall j :: 0 <= j < |input[k]| ==> 
                (input[k][j] != '?' ==> input[k][j] == solution[k][j]) &&
                (input[k][j] == '?' ==> solution[k][j] >= '0' && solution[k][j] <= '9'))
        invariant forall k :: 0 <= k < i ==> isValidPositiveInteger(solution[k])
        invariant forall k :: 0 <= k < i - 1 ==> isLexicographicallySmaller(solution[k], solution[k+1])
        invariant i > 0 ==> isLexicographicallySmaller(solution[i-1], current)
    {
        var nextStr := findNextValidString(input[i], current);
        if nextStr == "" {
            return false, [];
        }
        solution := solution + [nextStr];
        current := getNextMinimalString(nextStr);
    }
    
    return true, solution;
}

method findNextValidString(pattern: string, minStr: string) returns (result: string)
    requires |pattern| >= 1 && |pattern| <= 8
    requires forall j :: 0 <= j < |pattern| ==> 
        (pattern[j] >= '0' && pattern[j] <= '9') || pattern[j] == '?'
    requires isValidPositiveInteger(minStr)
    ensures result == "" || (
        |result| == |pattern| &&
        (forall j :: 0 <= j < |pattern| ==> 
            (pattern[j] != '?' ==> pattern[j] == result[j]) &&
            (pattern[j] == '?' ==> result[j] >= '0' && result[j] <= '9')) &&
        isValidPositiveInteger(result) &&
        isLexicographicallySmaller(minStr, result))
{
    if |pattern| < |minStr| {
        return "";
    }
    
    if |pattern| > |minStr| {
        var candidate := makeSmallestValid(pattern);
        if candidate != "" && isValidPositiveInteger(candidate) {
            return candidate;
        }
        return "";
    }
    
    var candidate := makeGreaterEqual(pattern, minStr);
    if candidate != "" && isValidPositiveInteger(candidate) && candidate > minStr {
        return candidate;
    }
    
    return "";
}

method makeSmallestValid(pattern: string) returns (result: string)
    requires |pattern| >= 1
    requires forall j :: 0 <= j < |pattern| ==> 
        (pattern[j] >= '0' && pattern[j] <= '9') || pattern[j] == '?'
    ensures |result| == |pattern| || result == ""
    ensures result != "" ==> 
        forall j :: 0 <= j < |pattern| ==> 
            (pattern[j] != '?' ==> pattern[j] == result[j]) &&
            (pattern[j] == '?' ==> result[j] >= '0' && result[j] <= '9')
{
    result := "";
    for i := 0 to |pattern|
        invariant |result| == i
        invariant forall j :: 0 <= j < i ==> 
            (pattern[j] != '?' ==> pattern[j] == result[j]) &&
            (pattern[j] == '?' ==> result[j] >= '0' && result[j] <= '9')
    {
        if pattern[i] == '?' {
            if i == 0 && |pattern| > 1 {
                result := result + "1";
            } else {
                result := result + "0";
            }
        } else {
            result := result + [pattern[i]];
        }
    }
    
    if |pattern| == 1 && result == "0" {
        result := "";
    } else if |pattern| > 1 && result[0] == '0' {
        result := "";
    }
}

method makeGreaterEqual(pattern: string, target: string) returns (result: string)
    requires |pattern| == |target|
    requires |pattern| >= 1
    requires forall j :: 0 <= j < |pattern| ==> 
        (pattern[j] >= '0' && pattern[j] <= '9') || pattern[j] == '?'
    requires isValidPositiveInteger(target)
    ensures |result| == |pattern| || result == ""
    ensures result != "" ==> 
        forall j :: 0 <= j < |pattern| ==> 
            (pattern[j] != '?' ==> pattern[j] == result[j]) &&
            (pattern[j] == '?' ==> result[j] >= '0' && result[j] <= '9')
{
    result := "";
    
    for i := 0 to |pattern|
        invariant |result| == i
        invariant forall j :: 0 <= j < i ==> 
            (pattern[j] != '?' ==> pattern[j] == result[j]) &&
            (pattern[j] == '?' ==> result[j] >= '0' && result[j] <= '9')
    {
        if pattern[i] == '?' {
            result := result + [target[i]];
        } else {
            if pattern[i] < target[i] {
                return "";
            }
            result := result + [pattern[i]];
        }
    }
    
    if result < target {
        result := incrementString(result, pattern, |pattern| - 1);
    }
}

method incrementString(current: string, pattern: string, pos: int) returns (result: string)
    requires |current| == |pattern|
    requires 0 <= pos < |pattern|
    requires forall j :: 0 <= j < |pattern| ==> 
        (pattern[j] >= '0' && pattern[j] <= '9') || pattern[j] == '?'
    requires forall j :: 0 <= j < |current| ==> current[j] >= '0' && current[j] <= '9'
    ensures result == "" || |result| == |pattern|
    decreases pos + 1
{
    if pos < 0 {
        return "";
    }
    
    if pattern[pos] == '?' {
        if current[pos] < '9' {
            var newChar := (current[pos] as int + 1) as char;
            result := current[..pos] + [newChar] + current[pos+1..];
            return result;
        } else {
            var prefix := incrementString(current, pattern, pos - 1);
            if prefix == "" {
                return "";
            }
            result := prefix[..pos] + "0" + prefix[pos+1..];
            return result;
        }
    } else {
        result := incrementString(current, pattern, pos - 1);
        return result;
    }
}

function getNextMinimalString(s: string): string
    requires isValidPositiveInteger(s)
    ensures isValidPositiveInteger(getNextMinimalString(s))
    ensures isLexicographicallySmaller(s, getNextMinimalString(s))
{
    s + "0"
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
        return "YES\n";
    }
    
    var inputStrings := lines[1..n+1];
    var success, solution := tryFindSolution(inputStrings);
    
    if !success {
        return "NO\n";
    }
    
    var output := "YES\n";
    for i := 0 to |solution|
        invariant |output| >= 4
        invariant output[..4] == "YES\n"
    {
        output := output + solution[i] + "\n";
    }
    
    return output;
}
// </vc-code>

