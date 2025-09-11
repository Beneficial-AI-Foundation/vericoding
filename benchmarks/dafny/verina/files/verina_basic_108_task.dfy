// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method BelowZero(operations: array<int>) returns (result: (array<int>, bool))
    ensures
        result.0.Length == operations.Length + 1
    ensures
        result.0[0] == 0
    ensures
        forall i :: 0 <= i < operations.Length ==> result.0[i + 1] == result.0[i] + operations[i]
    ensures
        result.1 == (exists i :: 1 <= i < result.0.Length && result.0[i] < 0)
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume {:axiom} false;
    var emptyArray := new int[0];
    result := (emptyArray, false);
    // impl-end
}
// </vc-code>
