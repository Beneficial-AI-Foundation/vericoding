// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method zeros(n: nat) returns (result: array<int>)
    ensures 
        result.Length == n &&
        (forall i :: 0 <= i < n ==> result[i] == 0)
{
    assume {:axiom} false;
}

method zeros2d(rows: nat, cols: nat) returns (result: array<array<int>>)
    ensures 
        result.Length == rows &&
        (forall i :: 0 <= i < rows ==> result[i].Length == cols) &&
        (forall i, j :: 0 <= i < rows && 0 <= j < cols ==> result[i][j] == 0)
{
    assume {:axiom} false;
}
// </vc-spec>
// <vc-code>
// </vc-code>
