// <vc-preamble>
predicate IsDigitSpec(c: char) 
{
    (c as int) >= 48 && (c as int) <= 57
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method IsInteger(text: array<char>) returns (result: bool)
    ensures result == (forall i :: 0 <= i < text.Length ==> IsDigitSpec(text[i]))
// </vc-spec>
// <vc-code>
{
    if text.Length == 0 {
        return true;
    }
    var i := 0;
    while i < text.Length
        invariant 0 <= i <= text.Length
        invariant forall j :: 0 <= j < i ==> IsDigitSpec(text[j])
    {
        if !IsDigitSpec(text[i]) {
            return false;
        }
        i := i + 1;
    }
    return true;
}
// </vc-code>
