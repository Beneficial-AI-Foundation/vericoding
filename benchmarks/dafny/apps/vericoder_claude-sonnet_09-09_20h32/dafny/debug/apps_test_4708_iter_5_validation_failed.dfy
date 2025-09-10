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
function SplitString(s: string, delim: char): seq<string>

function IsValidInteger(s: string): bool

function StringToInt(s: string): int
    requires IsValidInteger(s)

function IntToString(n: int): string

lemma {:axiom} SplitStringPreservesLength(s: string, delim: char)
    ensures var parts := SplitString(s, delim); |parts| >= 1

lemma {:axiom} ValidInputImpliesCorrectParsing(input: string)
    requires ValidInput(input)
    ensures var lines := SplitString(input, '\n');
            |lines| >= 4 &&
            IsValidInteger(lines[0]) &&
            IsValidInteger(lines[1]) &&
            IsValidInteger(lines[2]) &&
            IsValidInteger(lines[3])

lemma {:axiom} ValidOutputHelper(input: string, lines: seq<string>, N: int, K: int, X: int, Y: int, expectedAns: int)
    requires |lines| >= 4
    requires IsValidInteger(lines[0]) && IsValidInteger(lines[1]) && IsValidInteger(lines[2]) && IsValidInteger(lines[3])
    requires N == StringToInt(lines[0])
    requires K == StringToInt(lines[1])
    requires X == StringToInt(lines[2])
    requires Y == StringToInt(lines[3])
    requires expectedAns == (if K < N then K * X + (N - K) * Y else N * X)
    ensures ValidOutput(IntToString(expectedAns) + "\n", input)
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
    
    if |lines| < 4 {
        return "";
    }
    
    if !IsValidInteger(lines[0]) || !IsValidInteger(lines[1]) || 
       !IsValidInteger(lines[2]) || !IsValidInteger(lines[3]) {
        return "";
    }
    
    var N := StringToInt(lines[0]);
    var K := StringToInt(lines[1]);
    var X := StringToInt(lines[2]);
    var Y := StringToInt(lines[3]);
    
    var expectedAns := if K < N then K * X + (N - K) * Y else N * X;
    output := IntToString(expectedAns) + "\n";
    
    ValidOutputHelper(input, lines, N, K, X, Y, expectedAns);
}
// </vc-code>

