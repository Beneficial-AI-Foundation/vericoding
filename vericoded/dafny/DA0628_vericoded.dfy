predicate ValidInput(input: string)
{
    var parts := SplitStringFunc(input);
    |parts| >= 3 && 
    (forall i :: 0 <= i < 3 ==> |parts[i]| > 0 && IsValidInteger(parts[i])) &&
    var n := StringToIntFunc(parts[0]);
    var a := StringToIntFunc(parts[1]);
    var b := StringToIntFunc(parts[2]);
    1 <= n <= 20 && 1 <= a <= 100 && 1 <= b <= 2000
}

predicate IsValidInteger(s: string)
{
    |s| > 0 && 
    (s[0] == '-' || ('0' <= s[0] <= '9')) &&
    forall i :: 1 <= i < |s| ==> '0' <= s[i] <= '9'
}

function SplitStringFunc(s: string): seq<string>
{
    SplitStringHelper(s, 0, 0, [])
}

function SplitStringHelper(s: string, i: int, start: int, acc: seq<string>): seq<string>
requires 0 <= i <= |s|
requires 0 <= start <= |s|
decreases |s| - i
{
    if i == |s| then
        if i > start then acc + [s[start..i]] else acc
    else if s[i] == ' ' || s[i] == '\n' || s[i] == '\r' then
        var newAcc := if i > start then acc + [s[start..i]] else acc;
        SplitStringHelper(s, i + 1, i + 1, newAcc)
    else
        SplitStringHelper(s, i + 1, start, acc)
}

function StringToIntFunc(s: string): int
requires |s| > 0
requires IsValidInteger(s)
{
    if |s| > 0 && s[0] == '-' then
        -StringToIntHelper(s, 1, 0)
    else
        StringToIntHelper(s, 0, 0)
}

function StringToIntHelper(s: string, i: int, acc: int): int
requires 0 <= i <= |s|
decreases |s| - i
{
    if i == |s| then acc
    else if '0' <= s[i] <= '9' then
        StringToIntHelper(s, i + 1, acc * 10 + (s[i] as int - '0' as int))
    else
        StringToIntHelper(s, i + 1, acc)
}

function IntToStringFunc(n: int): string
{
    if n == 0 then "0"
    else if n < 0 then "-" + IntToStringHelper(-n, "")
    else IntToStringHelper(n, "")
}

function IntToStringHelper(n: int, acc: string): string
requires n >= 0
decreases n
{
    if n == 0 then acc
    else
        var digit := n % 10;
        IntToStringHelper(n / 10, [('0' as int + digit) as char] + acc)
}

function MinParkingCost(n: int, a: int, b: int): int
{
    var plan1Cost := n * a;
    var plan2Cost := b;
    if plan1Cost <= plan2Cost then plan1Cost else plan2Cost
}

// <vc-helpers>
// No additional helpers needed - all required functions are already provided in the preamble
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (result: string)
requires |input| > 0
requires ValidInput(input)
ensures exists n, a, b :: 
    var parts := SplitStringFunc(input);
    n == StringToIntFunc(parts[0]) &&
    a == StringToIntFunc(parts[1]) && 
    b == StringToIntFunc(parts[2]) &&
    result == IntToStringFunc(MinParkingCost(n, a, b)) + "\n"
// </vc-spec>
// <vc-code>
{
    var parts := SplitStringFunc(input);
    var n := StringToIntFunc(parts[0]);
    var a := StringToIntFunc(parts[1]);
    var b := StringToIntFunc(parts[2]);
    
    var minCost := MinParkingCost(n, a, b);
    result := IntToStringFunc(minCost) + "\n";
}
// </vc-code>

