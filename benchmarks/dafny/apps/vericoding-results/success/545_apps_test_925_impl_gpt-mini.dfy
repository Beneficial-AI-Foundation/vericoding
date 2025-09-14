predicate ValidInput(input: string)
{
    |input| >= 2 && 
    '0' <= input[0] <= '9' && 
    '0' <= input[1] <= '9' &&
    (input[|input|-1] == '\n' || (input[0] != '\n' && input[1] != '\n'))
}

function GoodDigitCount(digit: char): int
    requires '0' <= digit <= '9'
    ensures GoodDigitCount(digit) >= 1 && GoodDigitCount(digit) <= 7
{
    if digit == '0' then 2
    else if digit == '1' then 7
    else if digit == '2' then 2
    else if digit == '3' then 3
    else if digit == '4' then 3
    else if digit == '5' then 4
    else if digit == '6' then 2
    else if digit == '7' then 5
    else if digit == '8' then 1
    else 2
}

function ComputeTotalGoodCount(input: string): int
    requires ValidInput(input)
    ensures ComputeTotalGoodCount(input) >= 1 && ComputeTotalGoodCount(input) <= 49
{
    GoodDigitCount(input[0]) * GoodDigitCount(input[1])
}

predicate ValidOutput(result: string, expectedCount: int)
{
    |result| >= 2 && 
    result[|result|-1] == '\n' &&
    (forall c :: c in result ==> c == '\n' || ('0' <= c <= '9')) &&
    expectedCount >= 1 && expectedCount <= 49
}

// <vc-helpers>
function IntToString(n: int): string
    requires 1 <= n <= 49
    ensures |IntToString(n)| >= 1 && |IntToString(n)| <= 2
    ensures forall c :: c in IntToString(n) ==> '0' <= c <= '9'
{
    if n == 1 then "1" else
    if n == 2 then "2" else
    if n == 3 then "3" else
    if n == 4 then "4" else
    if n == 5 then "5" else
    if n == 6 then "6" else
    if n == 7 then "7" else
    if n == 8 then "8" else
    if n == 9 then "9" else
    if n == 10 then "10" else
    if n == 11 then "11" else
    if n == 12 then "12" else
    if n == 13 then "13" else
    if n == 14 then "14" else
    if n == 15 then "15" else
    if n == 16 then "16" else
    if n == 17 then "17" else
    if n == 18 then "18" else
    if n == 19 then "19" else
    if n == 20 then "20" else
    if n == 21 then "21" else
    if n == 22 then "22" else
    if n == 23 then "23" else
    if n == 24 then "24" else
    if n == 25 then "25" else
    if n == 26 then "26" else
    if n == 27 then "27" else
    if n == 28 then "28" else
    if n == 29 then "29" else
    if n == 30 then "30" else
    if n == 31 then "31" else
    if n == 32 then "32" else
    if n == 33 then "33" else
    if n == 34 then "34" else
    if n == 35 then "35" else
    if n == 36 then "36" else
    if n == 37 then "37" else
    if n == 38 then "38" else
    if n == 39 then "39" else
    if n == 40 then "40" else
    if n == 41 then "41" else
    if n == 42 then "42" else
    if n == 43 then "43" else
    if n == 44 then "44" else
    if n == 45 then "45" else
    if n == 46 then "46" else
    if n == 47 then "47" else
    if n == 48 then "48" else
    "49"
}
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (result: string)
    requires ValidInput(input)
    ensures ValidOutput(result, ComputeTotalGoodCount(input))
    ensures result == IntToString(ComputeTotalGoodCount(input)) + "\n"
// </vc-spec>
// <vc-code>
{
  var count := GoodDigitCount(input[0]) * GoodDigitCount(input[1]);
  result := IntToString(count) + "\n";
}
// </vc-code>

