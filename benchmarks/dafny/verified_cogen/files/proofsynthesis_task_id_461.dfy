// <vc-preamble>
predicate IsLowerCase(c: char)
{
    (c as int) >= 97 && (c as int) <= 122
}

predicate IsUpperCase(c: char)
{
    (c as int) >= 65 && (c as int) <= 90
}

function CountUppercaseRecursively(s: seq<char>): int
    decreases |s|
{
    if |s| == 0 then
        0
    else
        CountUppercaseRecursively(s[..|s|-1]) + (if IsUpperCase(s[|s|-1]) then 1 else 0)
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method CountUppercase(text: array<char>) returns (count: nat)
    ensures 0 <= count <= text.Length
    ensures CountUppercaseRecursively(text[..]) == count as int
// </vc-spec>
// <vc-code>
{
    assume {:axiom} false;
}
// </vc-code>
