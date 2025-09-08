Given a 2-digit number displayed on a 7-segment digital counter, count how many 
2-digit numbers (00-99) could have been the intended display before some light 
segments potentially broke (turned off). Segments can only break by turning OFF.

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

function IntToString(n: int): string
    requires n >= 0
    ensures |IntToString(n)| >= 1
    ensures forall c :: c in IntToString(n) ==> '0' <= c <= '9'
{
    if n == 0 then "0"
    else if n < 10 then [('0' as int + n) as char]
    else IntToString(n / 10) + IntToString(n % 10)
}

method solve(input: string) returns (result: string)
    requires ValidInput(input)
    ensures ValidOutput(result, ComputeTotalGoodCount(input))
    ensures result == IntToString(ComputeTotalGoodCount(input)) + "\n"
{
    var ngoods_0 := GoodDigitCount(input[0]);
    var ngoods_1 := GoodDigitCount(input[1]);
    var product := ngoods_0 * ngoods_1;
    result := IntToString(product) + "\n";
}
