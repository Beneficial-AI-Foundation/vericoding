// <vc-helpers>
// No additional helpers or proofs needed for this implementation
// </vc-helpers>

// <vc-spec>
// <vc-spec>
method CountCharacters(s: string) returns (count: int)
    ensures count >= 0
    ensures count == |s|
// </vc-spec>
// </vc-spec>

// <vc-code>
method CountCharactersImpl(s: string) returns (count: int)
    ensures count >= 0
    ensures count == |s|
{
    count := |s|;
}
// </vc-code>
