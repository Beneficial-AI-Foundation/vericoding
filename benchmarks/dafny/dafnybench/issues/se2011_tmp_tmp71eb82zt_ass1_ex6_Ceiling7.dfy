// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
// <vc-helpers>
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
method Ceiling7(n:nat) returns (k:nat)
requires n >= 0
ensures k == n-(n%7)
// </vc-spec>
// <vc-code>
{
    k := n-(n%7);
}
// </vc-code>
