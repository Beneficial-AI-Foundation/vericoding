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
lemma AllZeroStringImpliesStringToIntZero(s: string)
    requires |s| >= 0
    requires forall i :: 0 <= i < |s| ==> IsDigit(s[i]) && s[i] == '0'
    ensures StringToInt(s) == 0
    decreases |s|
{
    if |s| == 0 {
        assert StringToInt(s) == 0;
    } else {
        // s[0] == '0'
        assert DigitValue(s[0]) == 0;
        AllZeroStringImpliesStringToIntZero(s[1..]);
        assert StringToInt(s) == StringToInt(s[1..]) + DigitValue(s[0]) * Power10(|s|-1);
        assert DigitValue(s[0]) * Power10(|s|-1) == 0;
        assert StringToInt(s) == StringToInt(s[1..]);
        // by IH
        assert StringToInt(s) == 0;
    }
}

lemma SumOfDigits_ge_index(s: string, k: int)
    requires 0 <= k < |s|
    requires forall i :: 0 <= i < |s| ==> IsDigit(s[i])
    ensures SumOfDigits(s) >= DigitValue(s[k])
    decreases k
{
    if k == 0 {
        if |s| == 0 {
            // impossible because 0 <= k < |s|
        } else {
            // SumOfDigits(s) = DigitValue(s[0]) + SumOfDigits(s[1..])
            assert SumOfDigits(s) == DigitValue(s[0]) + SumOfDigits(s[1..]);
            assert SumOfDigits(s) >= DigitValue(s[0]);
        }
    } else {
        // k > 0
        // SumOfDigits(s) = DigitValue(s[0]) + SumOfDigits(s[1..])
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
        // From all digits being '0' we can derive StringToInt == 0
        AllZeroStringImpliesStringToIntZero(s);
        assert StringToInt(s) == 0;
        // But ValidPositiveIntegerString ensures StringToInt(s) > 0, contradiction
        assert false; // to discharge contradiction for verifier
    } else {
        // there exists an index with s[i] != '0'
        reveal_all: ;
        // Use logical reasoning to produce the witness
        var found := false;
        var idx := 0;
        while !found
            invariant !found ==> forall j :: 0 <= j < idx ==> s[j] == '0'
            invariant 0 <= idx <= |s|
        {
            if idx >= |s| {
                // should not happen because not all zero
                assert false;
            }
            if s[idx] != '0' {
                found := true;
            } else {
                idx := idx + 1;
            }
        }
        assert found && 0 <= idx < |s| && s[idx] != '0';
        // Provide the existential witness
        reveal_exist: ;
    }
}

lemma SumOfDigitsPositive(s: string)
    requires ValidPositiveIntegerString(s)
    ensures SumOfDigits(s) > 0
{
    // From ValidPositiveIntegerString there exists an index with non-'0' digit
    ExistsNonZeroDigit(s);
    var i := 0;
    // Find such index to use in proof
    var found := false;
    var idx := 0;
    while !found
        invariant !found ==> forall j :: 0 <= j < idx ==> s[j] == '0'
        invariant 0 <= idx <= |s|
    {
        if idx >= |s| {
            assert false;
        }
        if s[idx] != '0' {
            found := true;
        } else {
            idx := idx + 1;
        }
    }
    i := idx;
    // Now SumOfDigits(s) >= DigitValue(s[i]) by lemma
    SumOfDigits_ge_index(s, i);
    assert SumOfDigits(s) >= DigitValue(s[i]);
    // DigitValue(s[i]) > 0 because s[i] is a digit and not '0'
    assert IsDigit(s[i]);
    assert s[i] != '0';
    // Since '0' <= s[i] <= '9' and s[i] != '0' we have s[i] > '0', so DigitValue >= 1
    assert DigitValue(s[i]) >= 1;
    assert SumOfDigits(s) >= 1;
    assert SumOfDigits(s) > 0;
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

