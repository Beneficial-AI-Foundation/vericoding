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
function parseIntHelper(s: string, start: nat, index: nat): nat
    requires start <= index <= |s|
    decreases |s| - index
{
    if index == |s| then parseIntAcc(s, start, index, 0)
    else parseIntHelper(s, start, index + 1)
}

function parseIntAcc(s: string, start: nat, end: nat, acc: nat): nat
    requires start <= end <= |s|
    decreases end - start
{
    if start == end then acc
    else if start < |s| && '0' <= s[start] <= '9' then
        parseIntAcc(s, start + 1, end, acc * 10 + (s[start] - '0') as nat)
    else parseIntAcc(s, start + 1, end, acc)
}

lemma ParseIntHelperEquiv(s: string, index: nat)
    requires 0 <= index <= |s|
    ensures parseIntHelper(s, 0, index) == parseIntAcc(s, 0, index, 0)
{
    if index == 0 {
        assert parseIntHelper(s, 0, 0) == parseIntAcc(s, 0, 0, 0);
    } else {
        ParseIntHelperEquiv(s, index - 1);
    }
}

method parseInt(s: string) returns (n: nat)
    ensures n == parseIntHelper(s, 0, |s|)
{
    n := 0;
    var i := 0;
    while i < |s|
        invariant 0 <= i <= |s|
        invariant n == parseIntAcc(s, 0, i, 0)
    {
        if '0' <= s[i] <= '9' {
            n := n * 10 + (s[i] - '0') as nat;
        }
        i := i + 1;
    }
    ParseIntHelperEquiv(s, |s|);
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
    var n := parseInt(input[0]);
    
    var expected := buildExpectedPattern(input[1..n+1]);
    var message := input[n + 1];
    
    if isSubsequence(expected, message) {
        result := "yes";
    } else {
        result := "no";
    }
}
// </vc-code>

