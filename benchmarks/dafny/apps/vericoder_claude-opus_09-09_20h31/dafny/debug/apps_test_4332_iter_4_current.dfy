predicate IsDigit(c: char)
{
    '0' <= c <= '9'
}

function DigitValue(c: char): int
    requires IsDigit(c)
{
    c as int - '0' as int
}

function SumOfDigits(s: string): int
{
    if |s| == 0 then 0
    else if IsDigit(s[0]) then DigitValue(s[0]) + SumOfDigits(s[1..])
    else SumOfDigits(s[1..])
}

function StringToInt(s: string): int
{
    if |s| == 0 then 0
    else if IsDigit(s[0]) then StringToInt(s[1..]) + DigitValue(s[0]) * Power10(|s|-1)
    else StringToInt(s[1..])
}

function Power10(n: int): int
    requires n >= 0
{
    if n == 0 then 1 else 10 * Power10(n-1)
}

function CleanInput(input: string): string
{
    if |input| == 0 then ""
    else if input[|input|-1] == '\n' || input[|input|-1] == ' ' then CleanInput(input[..|input|-1])
    else input
}

predicate ValidPositiveIntegerString(s: string)
{
    |s| > 0 && (forall i :: 0 <= i < |s| ==> IsDigit(s[i])) && 
    (|s| > 1 ==> s[0] != '0') && 
    StringToInt(s) > 0
}

predicate ValidInput(input: string)
{
    ValidPositiveIntegerString(CleanInput(input))
}

// <vc-helpers>
lemma SumOfDigitsNonNegative(s: string)
    ensures SumOfDigits(s) >= 0
{
    if |s| == 0 {
        assert SumOfDigits(s) == 0;
    } else if IsDigit(s[0]) {
        SumOfDigitsNonNegative(s[1..]);
        assert SumOfDigits(s) == DigitValue(s[0]) + SumOfDigits(s[1..]);
        assert DigitValue(s[0]) >= 0;
        assert SumOfDigits(s[1..]) >= 0;
        assert SumOfDigits(s) >= 0;
    } else {
        SumOfDigitsNonNegative(s[1..]);
        assert SumOfDigits(s) == SumOfDigits(s[1..]);
        assert SumOfDigits(s) >= 0;
    }
}

lemma SumOfDigitsPositive(s: string)
    requires ValidPositiveIntegerString(s)
    ensures SumOfDigits(s) > 0
{
    assert |s| > 0;
    assert forall i :: 0 <= i < |s| ==> IsDigit(s[i]);
    
    if |s| == 1 {
        assert IsDigit(s[0]);
        assert s[0] != '0' by {
            if s[0] == '0' {
                assert StringToInt(s) == 0;
                assert false; // contradicts StringToInt(s) > 0
            }
        }
        assert DigitValue(s[0]) > 0;
        assert SumOfDigits(s) == DigitValue(s[0]);
    } else {
        assert s[0] != '0';
        assert IsDigit(s[0]);
        assert DigitValue(s[0]) > 0;
        SumOfDigitsNonNegative(s[1..]);
        assert SumOfDigits(s[1..]) >= 0;
        // By definition of SumOfDigits for when IsDigit(s[0]) is true:
        assert SumOfDigits(s) == DigitValue(s[0]) + SumOfDigits(s[1..]);
        // Since DigitValue(s[0]) > 0 and SumOfDigits(s[1..]) >= 0
        assert SumOfDigits(s) >= DigitValue(s[0]) > 0;
    }
}
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (result: string)
    requires ValidInput(input)
    ensures result == "Yes" || result == "No"
    ensures var cleaned := CleanInput(input);
            var n := StringToInt(cleaned);
            var digitSum := SumOfDigits(cleaned);
            digitSum > 0 && 
            ((result == "Yes") <==> (n % digitSum == 0)) &&
            ((result == "No") <==> (n % digitSum != 0))
    ensures var cleaned := CleanInput(input);
            var n := StringToInt(cleaned);
            n >= 1
// </vc-spec>
// <vc-code>
{
    var cleaned := CleanInput(input);
    var n := StringToInt(cleaned);
    var digitSum := SumOfDigits(cleaned);
    
    assert ValidPositiveIntegerString(cleaned);
    SumOfDigitsPositive(cleaned);
    assert digitSum > 0;
    
    if n % digitSum == 0 {
        result := "Yes";
    } else {
        result := "No";
    }
}
// </vc-code>

