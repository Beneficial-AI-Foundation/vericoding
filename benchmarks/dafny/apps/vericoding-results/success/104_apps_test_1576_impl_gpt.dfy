predicate ValidInput(t: string)
{
    |t| >= 1
}

// <vc-helpers>
// no helpers needed
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

