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
    var sums := new int[operations.Length + 1];
    var foundNegative := false;
    sums[0] := 0;
    var i := 0;
    while i < operations.Length
        invariant 0 <= i <= operations.Length
        invariant sums.Length == operations.Length + 1
        invariant sums[0] == 0
        invariant forall j :: 0 <= j < i ==> sums[j+1] == sums[j] + operations[j]
        invariant foundNegative <==> (exists j :: 1 <= j < i + 1 && sums[j] < 0)
    {
        sums[i+1] := sums[i] + operations[i];
        if sums[i+1] < 0 {
            foundNegative := true;
        }
        i := i + 1;
    }
    result := (sums, foundNegative);
}
// </vc-code>
