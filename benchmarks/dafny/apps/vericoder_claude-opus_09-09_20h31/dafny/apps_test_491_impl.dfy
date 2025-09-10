predicate ValidInput(n: int)
{
    n >= 10 || n <= -10
}

function MaxBalanceAfterOperation(n: int): int
    requires ValidInput(n)
{
    if n >= 0 then n
    else 
        var s := IntToString(n);
        var option1 := StringToInt(s[..|s|-1]);  // delete last digit
        var option2 := StringToInt(s[..|s|-2] + s[|s|-1..]);  // delete digit before last
        if option1 > option2 then option1 else option2
}

// <vc-helpers>
function IntToString(n: int): string
{
    if n == 0 then "0"
    else if n < 0 then "-" + NatToString(-n)
    else NatToString(n)
}

function NatToString(n: nat): string
    decreases n
{
    if n == 0 then ""
    else NatToString(n / 10) + DigitToChar(n % 10)
}

function DigitToChar(d: nat): string
    requires 0 <= d <= 9
{
    if d == 0 then "0"
    else if d == 1 then "1"
    else if d == 2 then "2"
    else if d == 3 then "3"
    else if d == 4 then "4"
    else if d == 5 then "5"
    else if d == 6 then "6"
    else if d == 7 then "7"
    else if d == 8 then "8"
    else "9"
}

function StringToInt(s: string): int
{
    if |s| == 0 then 0
    else if s[0] == '-' then -(StringToNat(s[1..]) as int)
    else StringToNat(s) as int
}

function StringToNat(s: string): nat
    decreases |s|
{
    if |s| == 0 then 0
    else CharToDigit(s[0]) * Power10(|s| - 1) + StringToNat(s[1..])
}

function CharToDigit(c: char): nat
{
    if c == '0' then 0
    else if c == '1' then 1
    else if c == '2' then 2
    else if c == '3' then 3
    else if c == '4' then 4
    else if c == '5' then 5
    else if c == '6' then 6
    else if c == '7' then 7
    else if c == '8' then 8
    else if c == '9' then 9
    else 0
}

function Power10(n: nat): nat
    decreases n
{
    if n == 0 then 1
    else 10 * Power10(n - 1)
}
// </vc-helpers>

// <vc-spec>
method solve(n: int) returns (result: int)
    requires ValidInput(n)
    ensures result == MaxBalanceAfterOperation(n)
// </vc-spec>
// <vc-code>
{
    if n >= 0 {
        result := n;
    } else {
        var s := IntToString(n);
        var option1 := StringToInt(s[..|s|-1]);
        var option2 := StringToInt(s[..|s|-2] + s[|s|-1..]);
        if option1 > option2 {
            result := option1;
        } else {
            result := option2;
        }
    }
}
// </vc-code>

