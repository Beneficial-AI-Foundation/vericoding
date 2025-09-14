

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method CountCharacters(s: string) returns (count: int)
    ensures count >= 0
    ensures count == |s|
// </vc-spec>
// <vc-code>
{
    var i := 0;
    var c := 0;
    while i < |s|
        invariant 0 <= i <= |s|
        invariant c == i
    {
        c := c + 1;
        i := i + 1;
    }
    return c;
}
// </vc-code>

