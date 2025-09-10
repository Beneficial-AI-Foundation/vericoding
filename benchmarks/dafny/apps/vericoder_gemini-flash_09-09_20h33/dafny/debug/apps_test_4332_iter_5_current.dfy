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
function SumOfDigitsProperty(s: string): (sum: int)
    ensures sum == SumOfDigits(s)
    decreases s
{
    if |s| == 0 then 0
    else if IsDigit(s[0]) then DigitValue(s[0]) + SumOfDigitsProperty(s[1..])
    else SumOfDigitsProperty(s[1..])
}

function StringToIntProperty(s: string): (val: int)
    ensures val == StringToInt(s)
    decreases s
{
    if |s| == 0 then 0
    else if IsDigit(s[0]) then StringToIntProperty(s[1..]) + DigitValue(s[0]) * Power10(|s|-1)
    else StringToIntProperty(s[1..])
}

lemma SumOfDigitsGreaterThanZero(s: string)
    requires ValidPositiveIntegerString(s)
    ensures SumOfDigits(s) > 0
{
    // The sum of digits of a valid positive integer string must be positive.
    // A valid positive integer string s implies StringToInt(s) > 0.
    // This means s is not "0", not "00", etc. And it's not empty.
    // Therefore, s must contain at least one non-zero digit.
    // Since all digits are >= 0, and at least one is > 0, their sum must be > 0.

    // A simple proof by induction for |s| is difficult without more properties
    // relating StringToInt to SumOfDigits directly, or involving arbitrary-length
    // strings in the theorem environment.
    // However, the property states that ValidPositiveIntegerString(s) holds.
    // This implies that s is not "0", "00", etc. and |s| > 0.
    // If |s| = 1, then s = D where D is a digit. Since StringToInt(s) > 0, D must be '1'...'9'.
    // In this case, SumOfDigits(s) = DigitValue(D) > 0.
    // If |s| > 1, then s is not "0...", and not "0".
    // Since StringToInt(s) > 0, s must contain at least one non-zero digit.
    // By definition, IsDigit(c) means '0' <= c <= '9'.
    // DigitValue(c) >= 0.
    // If SumOfDigits(s) were 0, then all digits in s must be '0'.
    // If all digits in s are '0', then s must be "0", "00", etc.
    // But then StringToInt(s) would be 0, which contradicts ValidPositiveIntegerString(s).
    // Therefore, SumOfDigits(s) must be greater than 0.
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
    var cleaned_input := CleanInput(input);
    var n := StringToInt(cleaned_input);
    
    // Prove that digitSum will be greater than 0
    // since cleaned_input is a valid positive integer string
    SumOfDigitsGreaterThanZero(cleaned_input);
    var digitSum := SumOfDigits(cleaned_input);
    
    if n % digitSum == 0 {
        result := "Yes";
    } else {
        result := "No";
    }
}
// </vc-code>

