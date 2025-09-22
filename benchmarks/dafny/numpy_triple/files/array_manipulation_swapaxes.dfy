// <vc-preamble>
// Predicate to check if a matrix has valid rectangular dimensions
predicate ValidMatrix(mat: seq<seq<real>>, rows: nat, cols: nat)
{
    |mat| == rows &&
    rows > 0 &&
    cols > 0 &&
    (forall i :: 0 <= i < rows ==> |mat[i]| == cols)
}

// Predicate to check if indices are valid for a 2D matrix (axes 0 and 1)
predicate ValidAxes(axis1: nat, axis2: nat)
{
    axis1 < 2 && axis2 < 2
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method SwapAxes(mat: seq<seq<real>>, axis1: nat, axis2: nat) returns (result: seq<seq<real>>)
    requires |mat| > 0
    requires forall i :: 0 <= i < |mat| ==> |mat[i]| > 0
    requires forall i :: 0 <= i < |mat| ==> |mat[i]| == |mat[0]|  // rectangular matrix
    requires ValidAxes(axis1, axis2)
    requires axis1 == 0 && axis2 == 1  // focus on transpose operation
    ensures ValidMatrix(result, |mat[0]|, |mat|)  // dimensions swapped
    ensures forall i, j :: 0 <= i < |mat| && 0 <= j < |mat[0]| ==> 
        mat[i][j] == result[j][i]  // element at (i,j) becomes element at (j,i)
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
