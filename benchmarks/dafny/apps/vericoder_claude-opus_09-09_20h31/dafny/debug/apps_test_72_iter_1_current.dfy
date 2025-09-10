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
function SplitLines(s: string): seq<string>
{
    SplitLinesHelper(s, 0, 0, [])
}

function SplitLinesHelper(s: string, start: nat, i: nat, acc: seq<string>): seq<string>
    requires start <= i <= |s|
    decreases |s| - i
{
    if i == |s| then
        acc + [s[start..i]]
    else if s[i] == '\n' then
        SplitLinesHelper(s, i + 1, i + 1, acc + [s[start..i]])
    else
        SplitLinesHelper(s, start, i + 1, acc)
}

function ParseInt(s: string): int
{
    if |s| == 0 then 0
    else ParseIntHelper(s, 0, 0)
}

function ParseIntHelper(s: string, i: nat, acc: int): int
    requires i <= |s|
    decreases |s| - i
{
    if i == |s| then acc
    else if '0' <= s[i] <= '9' then
        ParseIntHelper(s, i + 1, acc * 10 + (s[i] - '0') as int)
    else acc
}

function MaxCharFreq(s: string): int
    ensures MaxCharFreq(s) >= 0
    ensures MaxCharFreq(s) <= |s|
{
    if |s| == 0 then 0
    else MaxCharFreqForAllChars(s, s, 0)
}

function MaxCharFreqForAllChars(s: string, chars: string, i: nat): int
    requires i <= |chars|
    ensures MaxCharFreqForAllChars(s, chars, i) >= 0
    ensures MaxCharFreqForAllChars(s, chars, i) <= |s|
    decreases |chars| - i
{
    if i == |chars| then 0
    else Max(CountChar(s, chars[i]), MaxCharFreqForAllChars(s, chars, i + 1))
}

function CountChar(s: string, c: char): int
    ensures CountChar(s, c) >= 0
    ensures CountChar(s, c) <= |s|
{
    CountCharHelper(s, c, 0, 0)
}

function CountCharHelper(s: string, c: char, i: nat, acc: nat): int
    requires i <= |s|
    requires acc <= i
    ensures CountCharHelper(s, c, i, acc) >= 0
    ensures CountCharHelper(s, c, i, acc) <= |s|
    decreases |s| - i
{
    if i == |s| then acc
    else if s[i] == c then CountCharHelper(s, c, i + 1, acc + 1)
    else CountCharHelper(s, c, i + 1, acc)
}

function Max(a: int, b: int): int
{
    if a > b then a else b
}

function Max3(a: int, b: int, c: int): int
{
    Max(Max(a, b), c)
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
        return "";
    }
    
    var turns := ParseInt(lines[0]);
    var s0 := lines[1];
    var s1 := lines[2];
    var s2 := lines[3];
    
    var score0 := OptimalScore(s0, turns);
    var score1 := OptimalScore(s1, turns);
    var score2 := OptimalScore(s2, turns);
    
    var maxScore := Max3(score0, score1, score2);
    
    var winners := 0;
    if score0 == maxScore {
        winners := winners + 1;
    }
    if score1 == maxScore {
        winners := winners + 1;
    }
    if score2 == maxScore {
        winners := winners + 1;
    }
    
    if winners > 1 {
        return "Draw";
    } else if score0 == maxScore {
        return "Kuro";
    } else if score1 == maxScore {
        return "Shiro";
    } else {
        return "Katie";
    }
}
// </vc-code>

