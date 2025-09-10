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
function {:axiom} SplitLines(input: string): seq<string>
    ensures |SplitLines(input)| >= 0

function ParseInt(s: string): int

function {:axiom} MaxCharFreq(s: string): int
    ensures MaxCharFreq(s) >= 0
    ensures MaxCharFreq(s) <= |s|

function Max3(a: int, b: int, c: int): int
    ensures Max3(a, b, c) >= a && Max3(a, b, c) >= b && Max3(a, b, c) >= c
    ensures Max3(a, b, c) == a || Max3(a, b, c) == b || Max3(a, b, c) == c
{
    if a >= b && a >= c then a
    else if b >= c then b
    else c
}

lemma WinnersRange(score0: int, score1: int, score2: int, maxScore: int)
    requires maxScore >= score0 && maxScore >= score1 && maxScore >= score2
    requires maxScore == score0 || maxScore == score1 || maxScore == score2
    ensures var winners := (if score0 == maxScore then 1 else 0) + (if score1 == maxScore then 1 else 0) + (if score2 == maxScore then 1 else 0);
            winners >= 1 && winners <= 3
{
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
        if turns < 0 {
            result := "";
        } else {
            var s0 := lines[1];
            var s1 := lines[2]; 
            var s2 := lines[3];
            var score0 := OptimalScore(s0, turns);
            var score1 := OptimalScore(s1, turns);
            var score2 := OptimalScore(s2, turns);
            var maxScore := Max3(score0, score1, score2);
            var winners := (if score0 == maxScore then 1 else 0) + (if score1 == maxScore then 1 else 0) + (if score2 == maxScore then 1 else 0);
            
            WinnersRange(score0, score1, score2, maxScore);
            
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
}
// </vc-code>

