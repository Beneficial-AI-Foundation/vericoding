predicate ValidInput(input: string) {
    |input| >= 0
}

predicate ValidTestCase(n: int, a: int, b: int, c: int, d: int) {
    n >= 1 && n <= 1000 &&
    a >= 0 && a <= 1000 &&
    b >= 0 && b < a &&
    c >= 0 && c <= 1000 &&
    d >= 0 && d < c
}

function CanAchieveWeight(n: int, a: int, b: int, c: int, d: int): bool {
    var minWeight := (a - b) * n;
    var maxWeight := (a + b) * n;
    var targetMin := c - d;
    var targetMax := c + d;
    !(minWeight > targetMax || maxWeight < targetMin)
}

predicate ValidOutput(output: string) {
    forall i :: 0 <= i < |output| ==> output[i] in "YesNo\n"
}

// <vc-helpers>
function ParseInt(s: string): int
{
    if |s| == 0 then 0
    else if s[0] == '-' && |s| > 1 then -ParseIntHelper(s[1..])
    else ParseIntHelper(s)
}

function ParseIntHelper(s: string): int
{
    if |s| == 0 then 0
    else if |s| == 1 && '0' <= s[0] <= '9' then (s[0] as int) - ('0' as int)
    else if |s| > 1 && '0' <= s[0] <= '9' then 
        ((s[0] as int) - ('0' as int)) * Power10(|s| - 1) + ParseIntHelper(s[1..])
    else 0
}

function Power10(n: int): int
{
    if n <= 0 then 1
    else 10 * Power10(n - 1)
}

method SplitByWhitespace(s: string) returns (tokens: seq<string>)
{
    tokens := [];
    var i := 0;
    while i < |s|
        invariant 0 <= i <= |s|
    {
        if s[i] != ' ' && s[i] != '\n' && s[i] != '\t' && s[i] != '\r' {
            var start := i;
            while i < |s| && s[i] != ' ' && s[i] != '\n' && s[i] != '\t' && s[i] != '\r'
                invariant start <= i <= |s|
            {
                i := i + 1;
            }
            assert start <= i <= |s|;
            tokens := tokens + [s[start..i]];
        } else {
            i := i + 1;
        }
    }
}

lemma ValidOutputPreserved(s1: string, s2: string)
    requires ValidOutput(s1)
    requires s2 in ["Yes\n", "No\n"]
    ensures ValidOutput(s1 + s2)
{
    assert forall i :: 0 <= i < |s1| ==> (s1 + s2)[i] == s1[i];
    assert forall i :: |s1| <= i < |s1 + s2| ==> (s1 + s2)[i] == s2[i - |s1|];
}
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (result: string)
    requires ValidInput(input)
    ensures ValidOutput(result)
    ensures (input == "" || input == "\n") ==> result == ""
    ensures input != "" && input != "\n" ==> (|result| > 0 ==> result[|result|-1] == '\n' || (|result| > 3 && result[|result|-4..] in ["Yes\n", "No\n"]))
// </vc-spec>
// <vc-code>
{
    if input == "" || input == "\n" {
        return "";
    }
    
    var tokens := SplitByWhitespace(input);
    
    if |tokens| == 0 {
        return "";
    }
    
    var numCases := ParseInt(tokens[0]);
    result := "";
    
    var i := 1;
    var caseCount := 0;
    
    while i + 4 < |tokens| && caseCount < numCases
        invariant ValidOutput(result)
    {
        var n := ParseInt(tokens[i]);
        var a := ParseInt(tokens[i + 1]);
        var b := ParseInt(tokens[i + 2]);
        var c := ParseInt(tokens[i + 3]);
        var d := ParseInt(tokens[i + 4]);
        
        if CanAchieveWeight(n, a, b, c, d) {
            ValidOutputPreserved(result, "Yes\n");
            result := result + "Yes\n";
        } else {
            ValidOutputPreserved(result, "No\n");
            result := result + "No\n";
        }
        
        i := i + 5;
        caseCount := caseCount + 1;
    }
    
    if |result| > 0 {
        assert |result| >= 4;
        assert result[|result|-1] == '\n';
    }
}
// </vc-code>

