predicate ValidInput(input: string)
{
    var lines := SplitString(input, '\n');
    |lines| >= 4 &&
    IsValidInteger(lines[0]) &&
    IsValidInteger(lines[1]) &&
    IsValidInteger(lines[2]) &&
    IsValidInteger(lines[3]) &&
    var N := StringToInt(lines[0]);
    var K := StringToInt(lines[1]);
    var X := StringToInt(lines[2]);
    var Y := StringToInt(lines[3]);
    1 <= N <= 10000 && 1 <= K <= 10000 && 1 <= Y < X <= 10000
}

predicate ValidOutput(output: string, input: string)
{
    var lines := SplitString(input, '\n');
    if |lines| >= 4 && 
       IsValidInteger(lines[0]) &&
       IsValidInteger(lines[1]) &&
       IsValidInteger(lines[2]) &&
       IsValidInteger(lines[3]) then
        var N := StringToInt(lines[0]);
        var K := StringToInt(lines[1]);
        var X := StringToInt(lines[2]);
        var Y := StringToInt(lines[3]);
        var expectedAns := if K < N then K * X + (N - K) * Y else N * X;
        output == IntToString(expectedAns) + "\n"
    else
        output == ""
}

// <vc-helpers>
function method SplitString(s: string, sep: char): seq<string>
    ensures forall i | 0 <= i < |result| :: |result[i]| > 0 || result[i] == ""
    ensures forall i | 0 <= i < |result| :: (forall j | 0 <= j < |result[i]| :: result[i][j] != sep)

predicate method IsValidInteger(s: string) {
    |s| > 0 && (s[0] == '-' || '0' <= s[0] <= '9') &&
    (s[0] == '-' ==> |s| > 1) &&
    (forall i | 0 <= i < |s| :: '0' <= s[i] <= '9' || (i == 0 && s[i] == '-'))
}

function method StringToInt(s: string): int
    requires IsValidInteger(s)
    ensures var n := result; IntToString(n) == s

function method IntToString(n: int): string

lemma SplitStringProperties(s: string, sep: char)
    ensures var parts := SplitString(s, sep);
        forall i | 0 <= i < |parts| :: |parts[i]| > 0 || parts[i] == ""
    ensures var parts := SplitString(s, sep);
        forall i | 0 <= i < |parts| :: (forall j | 0 <= j < |parts[i]| :: parts[i][j] != sep)
        
lemma IntToStringValid(n: int)
    ensures IsValidInteger(IntToString(n))
    ensures StringToInt(IntToString(n)) == n
    
lemma StringToIntValid(s: string)
    requires IsValidInteger(s)
    ensures var n := StringToInt(s); IntToString(n) == s

lemma ArithmeticBounds(N: int, K: int, X: int, Y: int)
    requires 1 <= N <= 10000 && 1 <= K <= 10000 && 1 <= Y < X <= 10000
    ensures var ans := if K < N then K * X + (N - K) * Y else N * X;
        0 <= ans
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (output: string)
    requires |input| > 0
    ensures ValidOutput(output, input)
    ensures ValidInput(input) ==> 
        var lines := SplitString(input, '\n');
        var N := StringToInt(lines[0]);
        var K := StringToInt(lines[1]);
        var X := StringToInt(lines[2]);
        var Y := StringToInt(lines[3]);
        1 <= N <= 10000 && 1 <= K <= 10000 && 1 <= Y < X <= 10000 ==>
        var expectedAns := if K < N then K * X + (N - K) * Y else N * X;
        output == IntToString(expectedAns) + "\n"
// </vc-spec>
// <vc-code>
{
    var lines := SplitString(input, '\n');
    if |lines| >= 4 && IsValidInteger(lines[0]) && IsValidInteger(lines[1]) && IsValidInteger(lines[2]) && IsValidInteger(lines[3]) {
        var N := StringToInt(lines[0]);
        var K := StringToInt(lines[1]);
        var X := StringToInt(lines[2]);
        var Y := StringToInt(lines[3]);
        if 1 <= N <= 10000 && 1 <= K <= 10000 && 1 <= Y < X <= 10000 {
            var ans := if K < N then K * X + (N - K) * Y else N * X;
            output := IntToString(ans) + "\n";
        } else {
            output := "";
        }
    } else {
        output := "";
    }
}
// </vc-code>

