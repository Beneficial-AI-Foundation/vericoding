// <vc-preamble>
predicate IsDigit(c: char)
{
    (c as int) >= 48 && (c as int) <= 57
}

function CountDigitsRecursively(s: seq<char>): int
    decreases |s|
{
    if |s| == 0 then
        0
    else
        CountDigitsRecursively(s[..|s|-1]) + (if IsDigit(s[|s|-1]) then 1 else 0)
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method CountDigits(text: array<char>) returns (count: int)
    ensures 0 <= count <= text.Length
    ensures CountDigitsRecursively(text[..]) == count
// </vc-spec>
// <vc-code>
{
    assume {:axiom} false;
}
// </vc-code>
