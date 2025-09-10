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
  requires 0 <= n < 100
  decreases n
  ensures |IntToString(n)| >= 1
  ensures forall c :: c in IntToString(n) ==> '0' <= c <= '9'
  ensures n == 0 ==> IntToString(n) == "0"
{
  if n == 0 then
    "0"
  else
    IntToString(n / 10) + [(n % 10 + 48) as char]
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
  var count := ComputeTotalGoodCount(input);
  result := IntToString(count) + "\n";
}
// </vc-code>

