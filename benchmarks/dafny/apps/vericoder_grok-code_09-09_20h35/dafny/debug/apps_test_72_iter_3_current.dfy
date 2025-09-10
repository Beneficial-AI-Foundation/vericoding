predicate ValidInput(input: string) {
    |input| > 0
}

predicate ValidOutput(result: string) {
    result == "Kuro" || result == "Shiro" || result == "Katie" || result == "Draw" || result == ""
}

function OptimalScore(ribbon: string, turns: int): int
    requires |ribbon| >= 0 && turns >= 0
    ensures OptimalScore(ribbon, turns) >= 0
{
    var maxFreq := MaxCharFreq(ribbon);
    var length := |ribbon|;
    if turns == 1 && maxFreq == length then 
        if maxFreq > 0 then maxFreq - 1 else 0
    else if length < maxFreq + turns then length
    else maxFreq + turns
}

// <vc-helpers>
function Max(a: int, b: int): int { if a > b then a else b }

function Max3(a: int, b: int, c: int): int { Max(Max(a, b), c) }

function CountChar(c: char, s: string): int
    decreases |s|
{
    CountCharHelp(c, s, 0)
}

function CountCharHelp(c: char, s: string, i: int): int
    decreases |s| - i
{
    if i == |s| then 0
    else if s[i] == c then 1 + CountCharHelp(c, s, i+1) else CountCharHelp(c, s, i+1)
}

function MaxCharFreq(s: string): int
{
    if |s| == 0 then 0
    else Max(CountChar(s[0], s), MaxCharFreq(s[1..]))
}

function IndexOf(s: string, c: char, i: int): int
    requires 0 <= i <= |s|
    decreases |s|-i
{
    IndexOfHelp(s, c, i, |s|)
}

function IndexOfHelp(s: string, c: char, i: int, len: int): int
    decreases len - i
{
    if i == len then -1
    else if s[i] == c then i
    else IndexOfHelp(s, c, i+1, len)
}

function SplitLines(s: string): seq<string>
{
    SplitLinesHelp(s, 0)
}

function SplitLinesHelp(s: string, i: int): seq<string>
    decreases |s| - i
{
    if i == |s| then []
    else {
        var pos := IndexOf(s, '\n', i);
        if pos == -1 then [s[i..]]
        else [s[i..pos]] + SplitLinesHelp(s, pos+1)
    }
}

function ParseInt(s: string): int
    requires |s| > 0 && forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
{
    var n := 0;
    var i := 0;
    while i < |s|
    {
        n := n * 10 + (s[i] as int - '0' as int);
        i := i + 1;
    }
    n
}
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (result: string)
    requires ValidInput(input)
    ensures ValidOutput(result)
    ensures var lines := SplitLines(input);
            if |lines| < 4 then result == ""
            else (
                var turns := ParseInt(lines[0]);
                var s0 := lines[1];
                var s1 := lines[2]; 
                var s2 := lines[3];
                var score0 := OptimalScore(s0, turns);
                var score1 := OptimalScore(s1, turns);
                var score2 := OptimalScore(s2, turns);
                var maxScore := Max3(score0, score1, score2);
                var winners := (if score0 == maxScore then 1 else 0) + (if score1 == maxScore then 1 else 0) + (if score2 == maxScore then 1 else 0);
                (winners > 1 ==> result == "Draw") &&
                (winners == 1 && score0 == maxScore ==> result == "Kuro") &&
                (winners == 1 && score1 == maxScore ==> result == "Shiro") &&
                (winners == 1 && score2 == maxScore ==> result == "Katie")
            )
// </vc-spec>
// <vc-code>
{
    var lines := SplitLines(input);
    if |lines| < 4 {
        result := "";
    } else {
        var turns := ParseInt(lines[0]);
        var s0 := lines[1];
        var s1 := lines[2];
        var s2 := lines[3];
        var score0 := OptimalScore(s0, turns);
        var score1 := OptimalScore(s1, turns);
        var score2 := OptimalScore(s2, turns);
        var maxScore := Max3(score0, score1, score2);
        var winners := (if score0 == maxScore then 1 else 0) + (if score1 == maxScore then 1 else 0) + (if score2 == maxScore then 1 else 0);
        if winners > 1 {
            result := "Draw";
        } else if score0 == maxScore {
            result := "Kuro";
        } else if score1 == maxScore {
            result := "Shiro";
        } else {
            result := "Katie";
        }
    }
}
// </vc-code>

