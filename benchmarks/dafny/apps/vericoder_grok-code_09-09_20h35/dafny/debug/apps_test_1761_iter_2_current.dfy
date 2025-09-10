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
function parseIntHelper(s: string, index: nat, acc: nat): nat
    requires 0 <= index <= |s|
    requires forall i | index <= i < |s| :: '0' <= s[i] <= '9'
    decreases |s| - index
{
    if index == |s| then acc else parseIntHelper(s, index + 1, acc * 10 + ((s[index] as int) - ('0' as int)))
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
    var words := input[1..n + 1];
    var expected := buildExpectedPattern(words);
    var message := input[n + 1];
    if isSubsequence(expected, message) {
        result := "yes";
    } else {
        result := "no";
    }
}
// </vc-code>

