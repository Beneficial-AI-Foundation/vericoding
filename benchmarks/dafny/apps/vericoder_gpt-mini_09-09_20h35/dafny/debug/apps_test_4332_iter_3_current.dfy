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
lemma SumOfDigits_nonneg(s: string)
    requires forall i :: 0 <= i < |s| ==> IsDigit(s[i])
    ensures SumOfDigits(s) >= 0
    decreases |s|
{
    if |s| == 0 {
        assert SumOfDigits(s) == 0;
    } else {
        assert IsDigit(s[0]);
        // DigitValue(s[0]) >= 0
        assert DigitValue(s[0]) >= 0;
        SumOfDigits_nonneg(s[1..]);
        assert SumOfDigits(s) == DigitValue(s[0]) + SumOfDigits(s[1..]);
        assert SumOfDigits(s) >= 0;
    }
}

lemma SumOfDigits_ge_index(s: string, k: int)
    requires 0 <= k < |s|
    requires forall i :: 0 <= i < |s| ==> IsDigit(s[i])
    ensures SumOfDigits(s) >= DigitValue(s[k])
    decreases k
{
    if k == 0 {
        // |s| > 0 by precondition 0 <= k < |s|
        assert SumOfDigits(s) == DigitValue(s[0]) + SumOfDigits(s[1..]);
        // SumOfDigits(s[1..]) >= 0
        SumOfDigits_nonneg(s[1..]);
        assert SumOfDigits(s[1..]) >= 0;
        assert SumOfDigits(s) >= DigitValue(s[0]);
    } else {
        // k > 0
        assert SumOfDigits(s) == DigitValue(s[0]) + SumOfDigits(s[1..]);
        SumOfDigits_ge_index(s[1..], k-1);
        // From IH: SumOfDigits(s[1..]) >= DigitValue(s[k])
        assert SumOfDigits(s) >= DigitValue(s[k]);
    }
}

lemma ExistsNonZeroDigit(s: string)
    requires ValidPositiveIntegerString(s)
    ensures exists i :: 0 <= i < |s| && s[i] != '0'
{
    // If every digit were '0', StringToInt(s) would be 0, contradicting ValidPositiveIntegerString
    var allZero := (forall i :: 0 <= i < |s| ==> s[i] == '0');
    if allZero {
        AllZeroStringImpliesStringToIntZero(s);
        assert StringToInt(s) == 0;
        assert false;
    } else {
        var idx := 0;
        while idx < |s|
            invariant 0 <= idx <= |s|
            invariant forall j :: 0 <= j < idx ==> s[j] == '0'
            decreases |s| - idx
        {
            if s[idx] != '0' {
                assert 0 <= idx < |s| && s[idx] != '0';
                assert exists i :: 0 <= i < |s| && s[i] != '0';
                return;
            } else {
                idx := idx + 1;
            }
        }
        // Should not reach here because not all digits are '0'
        assert false;
    }
}

lemma SumOfDigitsPositive(s: string)
    requires ValidPositiveIntegerString(s)
    ensures SumOfDigits(s) > 0
{
    // Find an index with non-'0' digit
    var idx := 0;
    while idx < |s|
        invariant 0 <= idx <= |s|
        invariant forall j :: 0 <= j < idx ==> s[j] == '0'
        decreases |s| - idx
    {
        if s[idx] != '0' {
            // We have the witness idx
            assert 0 <= idx < |s| && s[idx] != '0';
            // SumOfDigits(s) >= DigitValue(s[idx])
            SumOfDigits_ge_index(s, idx);
            assert SumOfDigits(s) >= DigitValue(s[idx]);
            assert IsDigit(s[idx]);
            assert s[idx] != '0';
            assert DigitValue(s[idx]) >= 1;
            assert SumOfDigits(s) >= 1;
            assert SumOfDigits(s) > 0;
            return;
        } else {
            idx := idx + 1;
        }
    }
    // Should not reach here because ValidPositiveIntegerString ensures StringToInt(s) > 0,
    // hence not all digits are '0'
    ExistsNonZeroDigit(s);
    assert false;
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
    // Prove digitSum > 0 to allow modulus and satisfy postconditions
    SumOfDigitsPositive(cleaned);
    if n % digitSum == 0 {
        result := "Yes";
    } else {
        result := "No";
    }
}
// </vc-code>

