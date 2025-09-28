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
    var acc := new int[operations.Length + 1];
    acc[0] := 0;

    var foundBelowZero := false;

    var i := 0;
    while i < operations.Length
        invariant 0 <= i <= operations.Length
        invariant acc.Length == operations.Length + 1
        invariant acc[0] == 0
        invariant forall j :: 0 <= j < i ==> acc[j+1] == acc[j] + operations[j]
        invariant foundBelowZero == (exists j :: 1 <= j <= i && acc[j] < 0)
    {
        acc[i + 1] := acc[i] + operations[i];
        if acc[i + 1] < 0 {
            foundBelowZero := true;
        }
        i := i + 1;
    }

    result := (acc, foundBelowZero);
}
// </vc-code>
