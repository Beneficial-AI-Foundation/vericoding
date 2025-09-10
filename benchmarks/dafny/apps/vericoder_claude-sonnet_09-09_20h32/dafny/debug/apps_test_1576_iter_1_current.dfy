predicate ValidInput(t: string)
{
    |t| >= 1
}

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method solve(t: string) returns (result: string)
    requires ValidInput(t)
    ensures |result| == |t|
// </vc-spec>
// <vc-code>
{
    result := t;
}
// </vc-code>

