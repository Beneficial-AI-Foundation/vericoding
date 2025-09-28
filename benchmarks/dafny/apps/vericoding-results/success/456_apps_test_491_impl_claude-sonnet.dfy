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
    else if n > 0 then IntToStringPos(n)
    else "-" + IntToStringPos(-n)
}

function IntToStringPos(n: int): string
    requires n > 0
{
    if n < 10 then [DigitToChar(n)]
    else IntToStringPos(n / 10) + [DigitToChar(n % 10)]
}

function DigitToChar(d: int): char
    requires 0 <= d <= 9
{
    match d
        case 0 => '0'
        case 1 => '1'
        case 2 => '2'
        case 3 => '3'
        case 4 => '4'
        case 5 => '5'
        case 6 => '6'
        case 7 => '7'
        case 8 => '8'
        case 9 => '9'
}

function CharToDigit(c: char): int
{
    match c
        case '0' => 0
        case '1' => 1
        case '2' => 2
        case '3' => 3
        case '4' => 4
        case '5' => 5
        case '6' => 6
        case '7' => 7
        case '8' => 8
        case '9' => 9
        case _ => 0
}

function StringToInt(s: string): int
{
    if |s| == 0 then 0
    else if s[0] == '-' then -StringToIntPos(s[1..])
    else StringToIntPos(s)
}

function StringToIntPos(s: string): int
{
    if |s| == 0 then 0
    else if |s| == 1 then CharToDigit(s[0])
    else StringToIntPos(s[..|s|-1]) * 10 + CharToDigit(s[|s|-1])
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

