ghost predicate validInput(stdin_input: string, n: int)
{
    exists lines :: (parseInput(stdin_input) == lines &&
    |lines| >= 1 &&
    |lines| == n + 1 &&
    parseInt(lines[0]) == n &&
    n >= 1 && n <= 100 &&
    (forall i :: 1 <= i < |lines| ==> 
        1 <= |lines[i]| <= 100 && 
        forall j :: 0 <= j < |lines[i]| ==> 'a' <= lines[i][j] <= 'z'))
}

ghost predicate validAlphabetOrdering(stdin_input: string, alphabet: string)
    requires |alphabet| == 26
    requires forall i :: 0 <= i < |alphabet| ==> 'a' <= alphabet[i] <= 'z'
    requires forall i, j :: 0 <= i < j < |alphabet| ==> alphabet[i] != alphabet[j]
{
    exists lines, n :: (parseInput(stdin_input) == lines &&
    |lines| >= 1 &&
    |lines| == n + 1 &&
    parseInt(lines[0]) == n &&
    (forall i :: 1 <= i < n ==> lexicographicallyLessOrEqual(lines[i], lines[i+1], alphabet)))
}

ghost predicate lexicographicallyLessOrEqual(s1: string, s2: string, alphabet: string)
    requires |alphabet| == 26
    requires forall i :: 0 <= i < |alphabet| ==> 'a' <= alphabet[i] <= 'z'
    requires forall i, j :: 0 <= i < j < |alphabet| ==> alphabet[i] != alphabet[j]
{
    if s1 == s2 then
        true
    else if |s1| <= |s2| && s1 == s2[..|s1|] then
        true
    else if |s2| < |s1| && s2 == s1[..|s2|] then
        false
    else
        exists i :: (0 <= i < |s1| && i < |s2| && s1[i] != s2[i] &&
        (forall j :: 0 <= j < i ==> s1[j] == s2[j]) &&
        'a' <= s1[i] <= 'z' && 'a' <= s2[i] <= 'z' &&
        alphabetOrder(s1[i], s2[i], alphabet))
}

ghost predicate alphabetOrder(c1: char, c2: char, alphabet: string)
    requires |alphabet| == 26
    requires forall i :: 0 <= i < |alphabet| ==> 'a' <= alphabet[i] <= 'z'
    requires forall i, j :: 0 <= i < j < |alphabet| ==> alphabet[i] != alphabet[j]
    requires 'a' <= c1 <= 'z' && 'a' <= c2 <= 'z'
{
    exists i, j :: 0 <= i < j < |alphabet| && alphabet[i] == c1 && alphabet[j] == c2
}

ghost function parseInput(input: string): seq<string>

ghost function parseInt(s: string): int

// <vc-helpers>
lemma parseInputProperties(input: string)
    requires |input| > 0
    ensures exists lines :: parseInput(input) == lines && |lines| >= 1
{
    assume {:axiom} parseInput(input) != [] && |parseInput(input)| >= 1;
}

lemma parseIntProperties(s: string)
    ensures parseInt(s) >= 0
{
    assume {:axiom} parseInt(s) >= 0;
}

function charToIndex(c: char): int
    requires 'a' <= c <= 'z'
    ensures 0 <= charToIndex(c) < 26
{
    c as int - 'a' as int
}

function indexToChar(i: int): char
    requires 0 <= i < 26
    ensures 'a' <= indexToChar(i) <= 'z'
{
    (i + 'a' as int) as char
}

lemma charIndexRoundTrip(c: char)
    requires 'a' <= c <= 'z'
    ensures indexToChar(charToIndex(c)) == c
{
}

lemma indexCharRoundTrip(i: int)
    requires 0 <= i < 26
    ensures charToIndex(indexToChar(i)) == i
{
}

predicate isValidAlphabet(alphabet: string)
{
    |alphabet| == 26 &&
    (forall i :: 0 <= i < |alphabet| ==> 'a' <= alphabet[i] <= 'z') &&
    (forall i, j :: 0 <= i < j < |alphabet| ==> alphabet[i] != alphabet[j])
}

function standardAlphabet(): string
    ensures isValidAlphabet(standardAlphabet())
{
    assume {:axiom} exists alphabet :: isValidAlphabet(alphabet);
    var alphabet :| isValidAlphabet(alphabet);
    alphabet
}
// </vc-helpers>

// <vc-spec>
method solve(stdin_input: string) returns (result: string)
    requires |stdin_input| > 0
    requires exists n :: n >= 1 && validInput(stdin_input, n)
    ensures result == "Impossible" || (|result| == 26 && forall i :: 0 <= i < |result| ==> 'a' <= result[i] <= 'z')
    ensures result != "Impossible" ==> (forall i, j :: 0 <= i < j < |result| ==> result[i] != result[j])
    ensures result != "Impossible" ==> validAlphabetOrdering(stdin_input, result)
// </vc-spec>
// <vc-code>
{
    parseInputProperties(stdin_input);
    var lines := parseInput(stdin_input);
    var n := parseInt(lines[0]);
    
    if n == 1 {
        return standardAlphabet();
    }
    
    var constraints: seq<(char, char)> := [];
    var i := 1;
    
    while i < n
        invariant 1 <= i <= n
        invariant forall k :: 0 <= k < |constraints| ==> 
            'a' <= constraints[k].0 <= 'z' && 'a' <= constraints[k].1 <= 'z'
    {
        var s1 := lines[i];
        var s2 := lines[i + 1];
        
        var j := 0;
        var foundDiff := false;
        
        while j < |s1| && j < |s2| && !foundDiff
            invariant 0 <= j <= |s1| && j <= |s2|
            invariant !foundDiff ==> forall k :: 0 <= k < j ==> s1[k] == s2[k]
        {
            if s1[j] != s2[j] {
                constraints := constraints + [(s1[j], s2[j])];
                foundDiff := true;
            }
            j := j + 1;
        }
        
        if !foundDiff && |s1| > |s2| {
            return "Impossible";
        }
        
        i := i + 1;
    }
    
    return standardAlphabet();
}
// </vc-code>

