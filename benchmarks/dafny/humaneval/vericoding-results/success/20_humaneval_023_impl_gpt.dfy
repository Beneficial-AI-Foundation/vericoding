// <vc-preamble>

predicate ValidInput(s: string)
{
    true
}

function CorrectLength(s: string): int
{
    |s|
}
// </vc-preamble>

// <vc-helpers>
lemma CorrectLengthNonNegative(s: string)
  ensures CorrectLength(s) >= 0
{
}

// </vc-helpers>

// <vc-spec>
method strlen(s: string) returns (result: int)
    requires ValidInput(s)
    ensures result >= 0
    ensures result == CorrectLength(s)
// </vc-spec>
// <vc-code>
{
  result := CorrectLength(s);
}
// </vc-code>
