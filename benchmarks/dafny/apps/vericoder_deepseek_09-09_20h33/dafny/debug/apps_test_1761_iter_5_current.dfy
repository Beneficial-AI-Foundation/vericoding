predicate ValidInput(input: seq<string>)
{
    |input| >= 2 &&
    var n := parseIntHelper(input[0], 0, 0);
    n >= 1 && n + 1 < |input|
}

function buildExpectedPattern(words: seq<string>): seq<char>
{
    if |words| == 0 then ['<', '3']
    else ['<', '3'] + seq(|words[0]|, i requires 0 <= i < |words[0]| => words[0][i]) + buildExpectedPattern(words[1..])
}

function isSubsequence(pattern: seq<char>, text: string): bool
{
    isSubsequenceHelper(pattern, text, 0, 0)
}

function isSubsequenceHelper(pattern: seq<char>, text: string, patternIndex: nat, textIndex: nat): bool
    requires patternIndex <= |pattern|
    requires textIndex <= |text|
    decreases |text| - textIndex
{
    if patternIndex == |pattern| then true
    else if textIndex == |text| then false
    else if pattern[patternIndex] == text[textIndex] then
        isSubsequenceHelper(pattern, text, patternIndex + 1, textIndex + 1)
    else
        isSubsequenceHelper(pattern, text, patternIndex, textIndex + 1)
}

// <vc-helpers>
function parseIntHelper(s: string, i: nat, acc: nat): nat
    decreases |s| - i
{
    if i >= |s| then
        acc
    else
        var c := s[i];
        if '0' <= c <= '9' then
            var newAcc := acc * 10 + (c as int - '0' as int);
            parseIntHelper(s, i + 1, newAcc)
        else
            parseIntHelper(s, i + 1, acc)
}

lemma parseIntHelperNonNegative(s: string, i: nat, acc: nat)
    ensures parseIntHelper(s, i, acc) >= acc
    decreases |s| - i
{
    if i < |s| {
        var c := s[i];
        if '0' <= c <= '9' {
            var newAcc := acc * 10 + (c as int - '0' as int);
            parseIntHelperNonNegative(s, i + 1, newAcc);
        } else {
            parseIntHelperNonNegative(s, i + 1, acc);
        }
    }
}

lemma parseIntHelperValid(s: string, i: nat, acc: nat)
    ensures parseIntHelper(s, i, acc) >= 0
    decreases |s| - i
{
    if i < |s| {
        var c := s[i];
        if '0' <= c <= '9' {
            var newAcc := acc * 10 + (c as int - '0' as int);
            parseIntHelperValid(s, i + 1, newAcc);
        } else {
            parseIntHelperValid(s, i + 1, acc);
        }
    }
}

lemma buildExpectedPatternNonEmpty(words: seq<string>)
    ensures |buildExpectedPattern(words)| >= 2
    decreases |words|
{
    if |words| > 0 {
        buildExpectedPatternNonEmpty(words[1..]);
    }
}

lemma isSubsequenceHelperProgress(pattern: seq<char>, text: string, patternIndex: nat, textIndex: nat)
    requires patternIndex <= |pattern|
    requires textIndex <= |text|
    ensures isSubsequenceHelper(pattern, text, patternIndex, textIndex) == 
        (if patternIndex == |pattern| then true
         else if textIndex == |text| then false
         else if pattern[patternIndex] == text[textIndex] then
             isSubsequenceHelper(pattern, text, patternIndex + 1, textIndex + 1)
         else
             isSubsequenceHelper(pattern极 text, patternIndex, textIndex + 1))
    decreases |text| - textIndex
{
}

lemma isSubsequenceHelperComplete(pattern: seq<char>, text: string, patternIndex: nat, textIndex: nat)
    requires patternIndex <= |pattern|
    requires textIndex <= |text|
    ensures isSubsequenceHelper(pattern, text, patternIndex, textIndex) == 
        (exists i: nat :: textIndex <= i <= |text| && 
            (forall j: nat :: patternIndex <= j < |pattern| ==> 
                i + j - patternIndex < |text| && pattern[j] == text[i + j - patternIndex]))
    decreases |text| - textIndex
{
    if patternIndex == |pattern| {
        // Base case: empty pattern is always a subsequence
        assert isSubsequenceHelper(pattern, text, patternIndex, textIndex) == true;
    } else if textIndex == |text| {
        // Base case: empty text but non-empty pattern
        assert isSubsequenceHelper(pattern, text, patternIndex, textIndex) == false;
    } else if pattern[patternIndex] == text[textIndex] {
        isSubsequenceHelperComplete(pattern, text, patternIndex + 1, textIndex + 1);
    } else {
        isSubsequenceHelperComplete(pattern, text, patternIndex, textIndex + 1);
    }
}

lemma isSubsequenceHelperMonotonic(pattern: seq<char>, text: string, patternIndex: nat, textIndex1: nat, textIndex2: nat)
    requires patternIndex <= |pattern|
    requires textIndex1 <= textIndex2 <= |text|
    ensures isSubsequenceHelper(pattern, text, patternIndex, textIndex1) ==> isSubsequenceHelper(pattern, text, patternIndex, textIndex2)
    decreases |text| - textIndex1
{
    if textIndex1 == textIndex2 {
        // Trivial case
    } else if patternIndex == |pattern| {
        // true implies true
    } else if textIndex1 == |text| {
        // false implies anything
    } else {
        // Inductive case
        isSubsequenceHelperMonotonic(pattern, text, patternIndex, textIndex1 + 1, textIndex2);
        if pattern[patternIndex] == text[textIndex1] {
            if textIndex1 + 1 <= textIndex2 {
                isSubsequenceHelperMonotonic(pattern, text, patternIndex + 1, textIndex1 + 1, textIndex2);
            }
        }
    }
}
// </vc-helpers>

// <vc-spec>
method solve(input: seq<string>) returns (result: string)
    requires |input| >= 2
    requires ValidInput(input)
    ensures result == "yes" || result == "no"
    ensures result == "yes" <==> (
        ValidInput(input) &&
        var n := parseIntHelper(input[0], 0, 0);
        var expected := buildExpectedPattern(input[1..n+1]);
        var message := input[n + 1];
        isSubsequence(expected, message)
    )
// </vc-spec>
// <vc-code>
{
    var n := parseIntHelper(input[0], 0, 0);
    var expected := buildExpectedPattern(input[1..n+1]);
    var message := input[n + 1];
    
    if isSubsequence(expected, message) {
        result := "yes";
    } else {
        result := "no";
    }
}
// </vc-code>

