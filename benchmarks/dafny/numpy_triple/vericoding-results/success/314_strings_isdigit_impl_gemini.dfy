// <vc-preamble>
// Predicate to check if a character is a digit (0-9)
predicate IsDigitChar(c: char)
{
    '0' <= c <= '9'
}

// Predicate to check if all characters in a string are digits
predicate AllDigits(s: string)
{
    forall i :: 0 <= i < |s| ==> IsDigitChar(s[i])
}

// Predicate to check if a string satisfies the isdigit condition:
// non-empty and all characters are digits
predicate IsDigitString(s: string)
{
    |s| > 0 && AllDigits(s)
}
// </vc-preamble>

// <vc-helpers>
method ComputeIsDigitString(s: string) returns (res: bool)
    ensures res == IsDigitString(s)
{
    if |s| == 0 {
        return false;
    }
    var i := 0;
    while i < |s|
        invariant 0 <= i <= |s|
        invariant forall j :: 0 <= j < i ==> IsDigitChar(s[j])
    {
        if !IsDigitChar(s[i]) {
            return false;
        }
        i := i + 1;
    }
    return true;
}
// </vc-helpers>

// <vc-spec>
method IsDigit(a: seq<string>) returns (result: seq<bool>)
    ensures |result| == |a|
    ensures forall i :: 0 <= i < |a| ==> result[i] == IsDigitString(a[i])
// </vc-spec>
// <vc-code>
{
    result := [];
    var i := 0;
    while i < |a|
        invariant 0 <= i <= |a|
        invariant |result| == i
        invariant forall j :: 0 <= j < i ==> result[j] == IsDigitString(a[j])
    {
        var is_digit_s := ComputeIsDigitString(a[i]);
        result := result + [is_digit_s];
        i := i + 1;
    }
}
// </vc-code>
