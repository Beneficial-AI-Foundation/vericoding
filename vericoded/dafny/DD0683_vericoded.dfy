

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method CountNonEmptySubstrings(s: string) returns (count: int)
    ensures count >= 0
    ensures count == (|s| * (|s| + 1)) / 2 // Formula for the number of non-empty substrings of a string
// </vc-spec>
// <vc-code>
{
    count := (|s| * (|s| + 1)) / 2;
}
// </vc-code>

