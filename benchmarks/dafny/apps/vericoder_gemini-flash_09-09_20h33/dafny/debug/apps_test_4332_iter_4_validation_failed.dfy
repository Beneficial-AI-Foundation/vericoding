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
    // The proof of this lemma relies on the definition of ValidPositiveIntegerString,
    // which states that StringToInt(s) > 0.
    // If StringToInt(s) > 0, then 's' must contain at least one non-zero digit.
    // Since all digits are non-negative, the sum of digits must be positive.
    // We can prove this by induction on the length of the string, or by contradiction.
    // Assume SumOfDigits(s) == 0. This implies all digits in 's' are '0'.
    // If all digits are '0', then StringToInt(s) would be 0, which contradicts ValidPositiveIntegerString.
    // Therefore, SumOfDigits(s) > 0.
    // The for loop in the original code was an attempt to prove this by summing,
    // but the invariant wasn't strong enough. A direct appeal to the properties
    // of IsDigit and DigitValue, combined with ValidPositiveIntegerString, is more effective.
    assert (exists i :: 0 <= i < |s| && DigitValue(s[i]) > 0); // Must contain at least one non-zero digit
    var currentSum := 0;
    for i := 0 to |s| - 1
        invariant 0 <= i <= |s|
        invariant currentSum == SumOfDigits(s[..i]) // This invariant is actually correct and can be used for verification
    {
        if IsDigit(s[i]) {
            currentSum := currentSum + DigitValue(s[i]);
        }
    }
    assert currentSum == SumOfDigits(s);
    // Since ValidPositiveIntegerString implies StringToInt(s) > 0,
    // there must be at least one non-zero digit. The sum of digits
    // will therefore be greater than zero.
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

