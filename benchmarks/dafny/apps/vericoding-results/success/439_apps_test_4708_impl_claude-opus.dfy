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
function SplitString(s: string, delimiter: char): seq<string>
{
    SplitStringHelper(s, delimiter, 0, 0, [])
}

function SplitStringHelper(s: string, delimiter: char, start: int, current: int, acc: seq<string>): seq<string>
    requires 0 <= start <= current <= |s|
    decreases |s| - current
{
    if current == |s| then
        if start == current then acc
        else acc + [s[start..current]]
    else if s[current] == delimiter then
        SplitStringHelper(s, delimiter, current + 1, current + 1, acc + [s[start..current]])
    else
        SplitStringHelper(s, delimiter, start, current + 1, acc)
}

predicate IsValidInteger(s: string)
{
    |s| > 0 && 
    (s[0] == '-' ==> |s| > 1) &&
    forall i :: (if s[0] == '-' then 1 else 0) <= i < |s| ==> '0' <= s[i] <= '9'
}

function StringToInt(s: string): int
    requires IsValidInteger(s)
{
    if s[0] == '-' then
        -(StringToNat(s[1..]) as int)
    else
        StringToNat(s) as int
}

function StringToNat(s: string): nat
    requires |s| > 0
    requires forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
{
    if |s| == 1 then
        (s[0] - '0') as nat
    else
        StringToNat(s[..|s|-1]) * 10 + (s[|s|-1] - '0') as nat
}

function IntToString(n: int): string
{
    if n < 0 then
        "-" + NatToString((-n) as nat)
    else
        NatToString(n as nat)
}

function NatToString(n: nat): string
{
    if n < 10 then
        [(n as char + '0')]
    else
        NatToString(n / 10) + [(n % 10) as char + '0']
}
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
    
    if |lines| >= 4 && 
       IsValidInteger(lines[0]) &&
       IsValidInteger(lines[1]) &&
       IsValidInteger(lines[2]) &&
       IsValidInteger(lines[3]) {
        
        var N := StringToInt(lines[0]);
        var K := StringToInt(lines[1]);
        var X := StringToInt(lines[2]);
        var Y := StringToInt(lines[3]);
        
        var expectedAns := if K < N then K * X + (N - K) * Y else N * X;
        output := IntToString(expectedAns) + "\n";
    } else {
        output := "";
    }
}
// </vc-code>

