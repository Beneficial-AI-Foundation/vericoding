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

lemma ResultPropertiesAfterAppend(result: string, answer: string)
    requires answer in ["Yes\n", "No\n"]
    ensures |result + answer| >= 4
    ensures (result + answer)[|(result + answer)|-1] == '\n'
{
    assert |answer| == 4;
    assert |result + answer| == |result| + |answer| == |result| + 4 >= 4;
    assert answer[3] == '\n';
    assert (result + answer)[|(result + answer)|-1] == answer[|answer|-1] == answer[3] == '\n';
}

lemma AnswerLength(answer: string)
    requires answer in ["Yes\n", "No\n"]
    ensures |answer| == 4
{
    if answer == "Yes\n" {
        assert |"Yes\n"| == 4;
    } else {
        assert answer == "No\n";
        assert |"No\n"| == 3;
    }
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
        invariant |result| > 0 ==> |result| >= 4 && result[|result|-1] == '\n'
    {
        var n := ParseInt(tokens[i]);
        var a := ParseInt(tokens[i + 1]);
        var b := ParseInt(tokens[i + 2]);
        var c := ParseInt(tokens[i + 3]);
        var d := ParseInt(tokens[i + 4]);
        
        var answer: string;
        if CanAchieveWeight(n, a, b, c, d) {
            answer := "Yes\n";
        } else {
            answer := "No\n";
        }
        
        ValidOutputPreserved(result, answer);
        ResultPropertiesAfterAppend(result, answer);
        result := result + answer;
        
        i := i + 5;
        caseCount := caseCount + 1;
    }
}
// </vc-code>

