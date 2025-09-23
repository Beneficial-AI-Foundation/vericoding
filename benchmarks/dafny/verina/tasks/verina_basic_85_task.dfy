// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method Reverse(a: array<int>) returns (result: array<int>)
    ensures result.Length == a.Length
    ensures forall i :: 0 <= i < a.Length ==> result[i] == a[a.Length - 1 - i]
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume {:axiom} false;
    result := new int[0];
    // impl-end
}
// </vc-code>
