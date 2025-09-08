Given n words forming a message, determine if a received text could have been encoded by:
1. Creating coded string with "<3" before each word and after last word
2. Inserting additional characters anywhere in the coded string
Check if received message contains expected coded string as subsequence.

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

function parseIntHelper(s: string, pos: nat, acc: nat): nat
    requires pos <= |s|
    decreases |s| - pos
{
    if pos >= |s| then acc
    else if s[pos] >= '0' && s[pos] <= '9' then
        parseIntHelper(s, pos + 1, acc * 10 + (s[pos] as int - '0' as int))
    else
        parseIntHelper(s, pos + 1, acc)
}

method parseInt(s: string) returns (n: int)
    ensures n >= 0
    ensures n == parseIntHelper(s, 0, 0)
{
    n := parseIntHelper(s, 0, 0);
}

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
{
    if |input| == 0 {
        return "no";
    }

    var n := parseInt(input[0]);
    if n < 1 || n + 1 >= |input| {
        return "no";
    }

    var expected := buildExpectedPattern(input[1..n+1]);
    var message := input[n + 1];

    if isSubsequence(expected, message) {
        return "yes";
    } else {
        return "no";
    }
}
