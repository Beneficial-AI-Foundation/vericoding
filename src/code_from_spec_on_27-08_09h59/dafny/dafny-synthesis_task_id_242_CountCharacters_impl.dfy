// <vc-helpers>
// </vc-helpers>

// <vc-spec>
// <vc-spec>
method CountCharacters(s: string) returns (count: int)
    ensures count >= 0
    ensures count == |s|
// </vc-spec>
// </vc-spec>

// <vc-code>
{
    count := |s|;
}
// </vc-code>
