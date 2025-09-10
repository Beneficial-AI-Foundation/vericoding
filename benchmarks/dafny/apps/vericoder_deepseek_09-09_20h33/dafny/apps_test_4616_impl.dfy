predicate ValidInput(s: string)
{
    |s| >= 3 && |s| <= 100 && forall i :: 0 <= i < |s| ==> 'a' <= s[i] <= 'z'
}

predicate ValidAbbreviation(s: string, result: string)
{
    |result| >= 3 &&
    |s| >= 3 &&
    result[0] == s[0] &&
    result[|result|-1] == s[|s|-1] &&
    result == [s[0]] + IntToString(|s| - 2) + [s[|s|-1]]
}

function IntToString(n: int): string
{
    if n == 0 then "0"
    else if n < 0 then "-" + IntToStringHelper(-n)
    else IntToStringHelper(n)
}

function IntToStringHelper(n: int): string
    requires n >= 0
{
    if n == 0 then ""
    else IntToStringHelper(n / 10) + [(('0' as int) + (n % 10)) as char]
}

// <vc-helpers>
lemma {:induction false} IntToStringHelperNonNegative(n: int)
    requires n >= 0
    ensures |IntToStringHelper(n)| >= 0
{
}

lemma IntToStringHelperLength(n: int)
    requires n >= 0
    ensures n == 0 ==> |IntToStringHelper(n)| == 0
    ensures n > 0 && n < 10 ==> |IntToStringHelper(n)| == 1
    ensures n >= 10 ==> |IntToStringHelper(n)| > 0
{
    if n == 0 {
    } else if n < 10 {
        // n is between 1 and 9, so we return one character
    } else {
        IntToStringHelperLength(n / 10);
    }
}

lemma IntToStringLength(n: int)
    ensures n == 0 ==> |IntToString(n)| == 1
    ensures n > 0 && n < 10 ==> |IntToString(n)| == 1
    ensures n >= 10 ==> |IntToString(n)| >= 2
    ensures n < 0 ==> |IntToString(n)| >= 2
{
    if n == 0 {
    } else if n < 0 {
        var abs := -n;
        if abs < 10 {
            // Here we show that for negative single-digit numbers, the result has length 2 (e.g., "-5")
            assert |IntToStringHelper(abs)| == 1;
        } else {
            IntToStringHelperLength(abs);
        }
    } else {
        if n < 10 {
        } else {
            IntToStringHelperLength(n);
        }
    }
}

lemma IntToStringPositiveLength(n: int)
    ensures |IntToString(n)| > 0
{
    if n == 0 {
    } else if n < 0 {
        IntToStringHelperLength(-n);
    } else {
        IntToStringHelperLength(n);
    }
}
// </vc-helpers>

// <vc-spec>
method solve(s: string) returns (result: string)
    requires ValidInput(s)
    ensures ValidAbbreviation(s, result)
// </vc-spec>
// <vc-code>
{
    var len := |s|;
    var middle := len - 2;
    IntToStringLength(middle);
    var numStr := IntToString(middle);
    
    // Compute the result and verify its properties
    result := [s[0]] + numStr + [s[len - 1]];
    
    // The result string is constructed by concatenating three parts
    assert result == [s[0]] + numStr + [s[len - 1]];
    
    // First character of result is s[0]
    assert result[0] == s[0];
    
    // Last character of result is s[len-1]
    assert result[|result|-1] == s[len-1];
    
    // The numeric part is non-empty, ensuring overall length >= 3
    IntToStringPositiveLength(middle);
    assert |numStr| > 0;
    assert |result| == 1 + |numStr| + 1 == |numStr| + 2 >= 3;
    
    // Original string length is at least 3 by ValidInput
    assert |s| >= 3;
}
// </vc-code>

