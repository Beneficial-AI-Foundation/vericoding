// <vc-preamble>
// Method to construct the companion matrix of a polynomial
// Given coefficients c = [c0, c1, ..., cn, c_{n+1}] representing polynomial
// p(x) = c0 + c1*x + ... + c_{n+1}*x^{n+1}, returns the (n+1)×(n+1) companion matrix
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method PolyCompanion(c: seq<real>) returns (matrix: seq<seq<real>>)
    requires |c| >= 2  // Need at least 2 coefficients
    requires c[|c|-1] != 0.0  // Leading coefficient must be non-zero
    ensures |matrix| == |c| - 1  // Matrix is (n+1)×(n+1) for degree n+1 polynomial
    ensures forall i :: 0 <= i < |matrix| ==> |matrix[i]| == |c| - 1  // Square matrix
    ensures forall i, j :: 0 <= i < |matrix| - 1 && 0 <= j < |matrix[i]| ==>
        // First n rows: shifted identity pattern (1 in position i+1, 0 elsewhere)
        (matrix[i][j] == (if j == i + 1 then 1.0 else 0.0))
    ensures forall j :: 0 <= j < |matrix| - 1 ==>
        // Last row: normalized negative coefficients
        matrix[|matrix| - 1][j] == -c[j] / c[|c| - 1]
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
