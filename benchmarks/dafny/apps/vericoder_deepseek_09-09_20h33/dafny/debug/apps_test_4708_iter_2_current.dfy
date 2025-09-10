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
    ensures var n := StringToInt(s); IntToString(n) == s && IsValidInteger(s)

lemma ArithmeticBounds(N: int, K: int, X: int, Y: int)
    requires 1 <= N <= 10000 && 1 <= K <= 10000 && 1 <= Y < X <= 10000
    ensures var ans := if K < N then K * X + (N - K) * Y else N * X;
        0 <= ans < 10000 * 10000
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
    if |lines| >= 4 && IsValidInteger(lines[0]) && IsValidInteger(lines[1]) && IsValidInteger(lines[2]) && IsValidInteger(lines[3]) then {
        var N := StringToInt(lines[0]);
        var K := StringToInt(lines[1]);
        var X := StringToInt(lines[2]);
        var Y := StringToInt(lines[3]);
        if 1 <= N <= 10000 && 1 <= K <= 10000 && 1 <= Y < X <= 10000 then {
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

