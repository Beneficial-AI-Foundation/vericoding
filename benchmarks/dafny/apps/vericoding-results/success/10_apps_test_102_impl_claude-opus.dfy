predicate ValidInput(s: string)
{
    IsValidIntegerString(s) && 
    var n := ParseInteger(s); 0 <= n <= 99
}

function CorrectEnglishWord(n: int): string
    requires 0 <= n <= 99
{
    if n == 0 then "zero"
    else if n == 1 then "one"
    else if n == 2 then "two"
    else if n == 3 then "three"
    else if n == 4 then "four"
    else if n == 5 then "five"
    else if n == 6 then "six"
    else if n == 7 then "seven"
    else if n == 8 then "eight"
    else if n == 9 then "nine"
    else if n == 10 then "ten"
    else if n == 11 then "eleven"
    else if n == 12 then "twelve"
    else if n == 13 then "thirteen"
    else if n == 14 then "fourteen"
    else if n == 15 then "fifteen"
    else if n == 16 then "sixteen"
    else if n == 17 then "seventeen"
    else if n == 18 then "eighteen"
    else if n == 19 then "nineteen"
    else if n == 20 then "twenty"
    else if n == 30 then "thirty"
    else if n == 40 then "forty"
    else if n == 50 then "fifty"
    else if n == 60 then "sixty"
    else if n == 70 then "seventy"
    else if n == 80 then "eighty"
    else if n == 90 then "ninety"
    else if 21 <= n <= 29 then "twenty-" + UnitWord(n % 10)
    else if 31 <= n <= 39 then "thirty-" + UnitWord(n % 10)
    else if 41 <= n <= 49 then "forty-" + UnitWord(n % 10)
    else if 51 <= n <= 59 then "fifty-" + UnitWord(n % 10)
    else if 61 <= n <= 69 then "sixty-" + UnitWord(n % 10)
    else if 71 <= n <= 79 then "seventy-" + UnitWord(n % 10)
    else if 81 <= n <= 89 then "eighty-" + UnitWord(n % 10)
    else "ninety-" + UnitWord(n % 10)
}

predicate IsValidIntegerString(s: string)
{
    (|s| >= 1 && |s| <= 3 && forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9') ||
    (|s| >= 2 && |s| <= 4 && s[|s|-1] == '\n' && forall i :: 0 <= i < |s|-1 ==> '0' <= s[i] <= '9')
}

function ParseInteger(s: string): int
    requires IsValidIntegerString(s)
{
    if s[|s|-1] == '\n' then
        ParseIntegerHelper(s[0..|s|-1])
    else
        ParseIntegerHelper(s)
}

function ParseIntegerHelper(s: string): int
    requires |s| >= 1 && |s| <= 3
    requires forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
{
    if |s| == 1 then
        (s[0] as int) - ('0' as int)
    else if |s| == 2 then
        10 * ((s[0] as int) - ('0' as int)) + ((s[1] as int) - ('0' as int))
    else
        100 * ((s[0] as int) - ('0' as int)) + 10 * ((s[1] as int) - ('0' as int)) + ((s[2] as int) - ('0' as int))
}

// <vc-helpers>
function UnitWord(n: int): string
    requires 1 <= n <= 9
{
    if n == 1 then "one"
    else if n == 2 then "two"
    else if n == 3 then "three"
    else if n == 4 then "four"
    else if n == 5 then "five"
    else if n == 6 then "six"
    else if n == 7 then "seven"
    else if n == 8 then "eight"
    else "nine"
}
// </vc-helpers>

// <vc-spec>
method solve(stdin_input: string) returns (result: string)
    requires |stdin_input| > 0
    requires ValidInput(stdin_input)
    ensures |result| > 0
    ensures result[|result|-1] == '\n'
    ensures var n := ParseInteger(stdin_input);
        result == CorrectEnglishWord(n) + "\n"
// </vc-spec>
// <vc-code>
{
    var n := ParseInteger(stdin_input);
    var word := CorrectEnglishWord(n);
    result := word + "\n";
}
// </vc-code>

