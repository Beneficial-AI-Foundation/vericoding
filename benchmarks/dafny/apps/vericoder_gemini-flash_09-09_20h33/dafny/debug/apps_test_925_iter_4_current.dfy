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
function IntToString(input: int): string
    requires input >= 0
    ensures (var s := IntToString(input); (input == 0 ==> s == "0") && (input > 0 ==> (s != "" && forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9')))
    ensures (input == 0 ==> |s| == 1)
    ensures (input > 0 ==> |s| > 0)
    ensures (input > 0 ==> (s != "" && s[0] != '0'))
{
    if input == 0 then
        "0"
    else
        var s := "";
        var temp := input;
        while temp > 0
            invariant temp >= 0
            invariant forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
            decreases temp
        {
            s := D_to_char(temp % 10) + s;
            temp := temp / 10;
        }
        s
}

function D_to_char(d: int): char
    requires 0 <= d <= 9
    ensures '0' <= D_to_char(d) <= '9'
{
    ('0' as int + d) as char
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
    var totalGoodCount := ComputeTotalGoodCount(input);
    result := IntToString(totalGoodCount) + "\n";
}
// </vc-code>

