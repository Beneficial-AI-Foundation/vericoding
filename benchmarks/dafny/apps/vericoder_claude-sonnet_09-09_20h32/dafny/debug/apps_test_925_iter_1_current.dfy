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
    ensures |IntToString(n)| >= 1
    ensures |IntToString(n)| <= 2
    ensures forall c :: c in IntToString(n) ==> '0' <= c <= '9'
    ensures StringToInt(IntToString(n)) == n
{
    if n < 10 then [('0' as int + n) as char]
    else [('0' as int + n / 10) as char, ('0' as int + n % 10) as char]
}

function StringToInt(s: string): int
    requires |s| >= 1 && |s| <= 2
    requires forall c :: c in s ==> '0' <= c <= '9'
    ensures 0 <= StringToInt(s) <= 99
{
    if |s| == 1 then (s[0] as int - '0' as int)
    else (s[0] as int - '0' as int) * 10 + (s[1] as int - '0' as int)
}

lemma IntToStringCorrect(n: int)
    requires 1 <= n <= 49
    ensures StringToInt(IntToString(n)) == n
{
    if n < 10 {
        assert IntToString(n) == [('0' as int + n) as char];
        assert StringToInt(IntToString(n)) == (('0' as int + n) as char) as int - '0' as int;
        assert (('0' as int + n) as char) as int == '0' as int + n;
        assert StringToInt(IntToString(n)) == n;
    } else {
        assert IntToString(n) == [('0' as int + n / 10) as char, ('0' as int + n % 10) as char];
        var s := IntToString(n);
        assert |s| == 2;
        assert StringToInt(s) == (s[0] as int - '0' as int) * 10 + (s[1] as int - '0' as int);
        assert s[0] == ('0' as int + n / 10) as char;
        assert s[1] == ('0' as int + n % 10) as char;
        assert (s[0] as int - '0' as int) == n / 10;
        assert (s[1] as int - '0' as int) == n % 10;
        assert StringToInt(s) == (n / 10) * 10 + (n % 10) == n;
    }
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
    var countStr := IntToString(count);
    result := countStr + "\n";
    
    IntToStringCorrect(count);
}
// </vc-code>

