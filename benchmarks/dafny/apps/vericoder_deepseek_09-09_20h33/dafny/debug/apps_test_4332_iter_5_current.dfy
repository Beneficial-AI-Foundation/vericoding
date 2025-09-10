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
lemma Power10Pos(n: int)
    requires n >= 0
    ensures Power10(n) > 0
{
    if n > 0 {
        Power10Pos(n-1);
    }
}

lemma StringToIntNonNegative(s: string)
    ensures StringToInt(s) >= 0
{
    // Proof by induction on string length
    if |s| == 0 {
        // Base case: empty string gives 0
    } else {
        // Recursive case: either we add a digit or skip non-digit
        StringToIntNonNegative(s[1..]);
        if IsDigit(s[0]) {
            Power10Pos(|s|-1);
        }
    }
}

lemma DigitSumNonNegative(s: string)
    ensures SumOfDigits(s) >= 0
{
    if |s| > 0 {
        DigitSumNonNegative(s[1..]);
    }
}

lemma ValidInputImpliesNonEmptyAndDigits(s: string)
    requires ValidInput(s)
    ensures |CleanInput(s)| > 0
    ensures forall i :: 0 <= i < |CleanInput(s)| ==> IsDigit(CleanInput(s)[i])
{
    // This follows from the definition of ValidInput and ValidPositiveIntegerString
}

lemma ValidInputImpliesNoLeadingZero(s: string)
    requires ValidInput(s)
    ensures var cleaned := CleanInput(s);
            |cleaned| == 1 || cleaned[0] != '0'
{
    // This follows from the definition of ValidPositiveIntegerString
}

lemma StringToIntPositive(s: string)
    requires ValidInput(s)
    ensures StringToInt(CleanInput(s)) > 0
{
}

lemma ValidInputImpliesPositiveDigitSum(s: string)
    requires ValidInput(s)
    ensures var cleaned := CleanInput(s);
            SumOfDigits(cleaned) > 0
{
    var cleaned := CleanInput(s);
    assert |cleaned| > 0;
    assert forall i :: 0 <= i < |cleaned| ==> IsDigit(cleaned[i]);
    ValidInputImpliesNoLeadingZero(s);
    
    // Prove by induction that at least one digit is non-zero
    var has_non_zero_digit := exists i :: 0 <= i < |cleaned| && cleaned[i] != '0';
    if !has_non_zero_digit {
        // All digits are '0', but this contradicts StringToInt(cleaned) > 0
        StringToIntPositive(s);
        assert StringToInt(cleaned) > 0;
        // However, if all digits are '0', StringToInt would return 0
        assert StringToInt(cleaned) == 0;
        assert false; // Contradiction
    }
    
    // Now we know there's at least one non-zero digit, so sum > 0
    var sum := SumOfDigits(cleaned);
    assert sum > 0 by {
        forall i | 0 <= i < |cleaned| && cleaned[i] != '0'
            ensures DigitValue(cleaned[i]) > 0;
        
        // The sum is at least the value of the smallest non-zero digit (which is 1)
        // and other digits are non-negative, so total sum is positive
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
    
    ValidInputImpliesPositiveDigitSum(input);
    assert digitSum > 0;
    
    if n % digitSum == 0 {
        result := "Yes";
    } else {
        result := "No";
    }
}
// </vc-code>

