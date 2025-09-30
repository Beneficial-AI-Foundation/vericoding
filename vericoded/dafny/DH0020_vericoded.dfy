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

// </vc-helpers>

// <vc-spec>
method strlen(s: string) returns (result: int)
    requires ValidInput(s)
    ensures result >= 0
    ensures result == CorrectLength(s)
// </vc-spec>
// <vc-code>
{
  result := |s|;
}
// </vc-code>
