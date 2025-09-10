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
function MaxCharFreq(s: string): (freq: int)
    requires |s| >= 0
    ensures freq >= 0
{
    if |s| == 0 then 0
    else var charCounts := CountChars(s);
         var max := 0;
         var i := 0;
         while i < 256
            invariant 0 <= i <= 256
            invariant max >= 0
            invariant forall j :: 0 <= j < i ==> charCounts[j] <= max
         {
            if charCounts[i] > max {
                max := charCounts[i];
            }
            i := i + 1;
         }
         max
}

function method CountChars(s: string): (arr: array<int>)
    requires |s| >= 0
    ensures arr.Length == 256
    ensures forall i :: 0 <= i < 256 ==> arr[i] >= 0
{
    var counts := new int[256](0);
    var i := 0;
    while i < |s|
        invariant 0 <= i <= |s|
        invariant forall j :: 0 <= j < 256 ==> counts[j] >= 0
        invariant forall j :: 0 <= j < i ==> 0 <= s[j] as int < 256
    {
        var c := s[i] as int;
        if c < 0 || c >= 256 {
            c := 0;
        }
        counts[c] := counts[c] + 1;
        i := i + 1;
    }
    counts
}

function Max3(a: int, b: int, c: int): (m: int)
    ensures m >= a && m >= b && m >= c
    ensures m == a || m == b || m == c
{
    if a >= b && a >= c then a
    else if b >= a && b >= c then b
    else c
}

function SplitLines(s: string): (lines: seq<string>)
    ensures |lines| >= 1
{
    var result: seq<string> := [];
    var start := 0;
    var i := 0;
    while i < |s|
        invariant 0 <= start <= i <= |s|
        invariant forall line in result :: |line| >= 0
    {
        if s[i] == '\n' {
            result := result + [s[start..i]];
            start := i + 1;
        }
        i := i + 1;
    }
    result := result + [s[start..|s|]];
    result
}

function ParseInt(s: string): (n: int)
    requires |s| > 0
    ensures n >= 0
{
    var result := 0;
    var i := 0;
    while i < |s|
        invariant 0 <= i <= |s|
        invariant result >= 0
        invariant forall j :: 0 <= j < i ==> '0' <= s[j] <= '9'
    {
        var digit := s[i] as int - '0' as int;
        if digit >= 0 && digit <= 9 {
            result := result * 10 + digit;
        }
        i := i + 1;
    }
    result
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
        return;
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
    if score0 == maxScore { winners := winners + 1; }
    if score1 == maxScore { winners := winners + 1; }
    if score2 == maxScore { winners := winners + 1; }
    
    if winners > 1 {
        result := "Draw";
    } else {
        if winners == 1 {
            if score0 == maxScore {
                result := "Kuro";
            } else if score1 == maxScore {
                result := "Shiro";
            } else {
                result := "Katie";
            }
        } else {
            result := "Draw";
        }
    }
}
// </vc-code>

