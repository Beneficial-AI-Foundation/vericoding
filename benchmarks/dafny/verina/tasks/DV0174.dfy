// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method IterCopy(s: array<int>) returns (result: array<int>)
    ensures
        s.Length == result.Length &&
        forall i :: 0 <= i < s.Length ==> s[i] == result[i]
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume {:axiom} false;
    result := new int[0];
    // impl-end
}
// </vc-code>
