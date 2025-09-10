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

lemma ParseIntHelperRecursive(s: string, index: nat)
    requires 0 <= index <= |s|
    ensures parseIntHelper(s, 0, index) == parseIntAcc(s, 0, |s|, 0)
    decreases |s| - index
{
    if index == |s| {
        assert parseIntHelper(s, 0, |s|) == parseIntAcc(s, 0, |s|, 0);
    } else {
        ParseIntHelperRecursive(s, index + 1);
    }
}

lemma ParseIntHelperEquiv(s: string)
    ensures parseIntHelper(s, 0, 0) == parseIntHelper(s, 0, |s|)
    ensures parseIntHelper(s, 0, |s|) == parseIntAcc(s, 0, |s|, 0)
{
    ParseIntHelperRecursive(s, 0);
    assert parseIntHelper(s, 0, 0) == parseIntAcc(s, 0, |s|, 0);
    assert parseIntHelper(s, 0, |s|) == parseIntAcc(s, 0, |s|, 0);
}

lemma ParseIntAccAccumulates(s: string, i: nat, acc: nat)
    requires 0 <= i < |s|
    requires '0' <= s[i] <= '9'
    ensures parseIntAcc(s, i, |s|, acc) == parseIntAcc(s, i + 1, |s|, acc * 10 + (s[i] - '0') as nat)
{
}

lemma ParseIntAccSkips(s: string, i: nat, acc: nat)
    requires 0 <= i < |s|
    requires !(s[i] >= '0' && s[i] <= '9')
    ensures parseIntAcc(s, i, |s|, acc) == parseIntAcc(s, i + 1, |s|, acc)
{
}

method parseInt(s: string) returns (n: nat)
    ensures n == parseIntHelper(s, 0, |s|)
    ensures n == parseIntHelper(s, 0, 0)
{
    n := 0;
    var i := 0;
    
    while i < |s|
        invariant 0 <= i <= |s|
        invariant n == parseIntAcc(s, 0, i, 0)
        decreases |s| - i
    {
        var old_n := n;
        if '0' <= s[i] <= '9' {
            n := n * 10 + (s[i] - '0') as nat;
        }
        
        assert parseIntAcc(s, 0, i + 1, 0) == 
               if i < |s| && '0' <= s[i] <= '9' then 
                   parseIntAcc(s, 0, i, 0) * 10 + (s[i] - '0') as nat
               else 
                   parseIntAcc(s, 0, i, 0);
        
        i := i + 1;
    }
    
    assert i == |s|;
    assert n == parseIntAcc(s, 0, |s|, 0);
    ParseIntHelperEquiv(s);
    assert n == parseIntHelper(s, 0, |s|);
    assert n == parseIntHelper(s, 0, 0);
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
    
    // parseInt ensures n == parseIntHelper(input[0], 0, 0)
    assert n == parseIntHelper(input[0], 0, 0);
    
    // From ValidInput, we know n satisfies the bounds
    assert n >= 1 && n + 1 < |input|;
    
    var expected := buildExpectedPattern(input[1..n+1]);
    var message := input[n + 1];
    
    if isSubsequence(expected, message) {
        result := "yes";
    } else {
        result := "no";
    }
}
// </vc-code>

