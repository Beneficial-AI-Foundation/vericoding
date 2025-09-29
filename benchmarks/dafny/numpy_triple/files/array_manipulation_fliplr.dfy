// <vc-preamble>
/*
 * Specification for numpy.fliplr: Reverse the order of elements along axis 1 (left/right).
 * This function flips a 2D matrix horizontally, reversing the column order in each row
 * while preserving the row order and the elements within each row.
 */

// Predicate to check if a 2D matrix is well-formed (rectangular)
predicate IsWellFormedMatrix<T>(m: seq<seq<T>>)
{
    |m| > 0 && 
    (forall i :: 0 <= i < |m| ==> |m[i]| == |m[0]|) &&
    |m[0]| > 0
}

// Predicate to check if two rows contain the same multiset of elements
predicate SameElements<T(==)>(row1: seq<T>, row2: seq<T>)
{
    multiset(row1) == multiset(row2)
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method FlipLR(m: seq<seq<real>>) returns (result: seq<seq<real>>)
    requires IsWellFormedMatrix(m)
    requires |m| >= 1 && |m[0]| >= 1  // At least 2D matrix
    ensures IsWellFormedMatrix(result)
    ensures |result| == |m|
    ensures |result[0]| == |m[0]|
    // Element mapping: result[i][j] == m[i][cols-1-j]
    ensures forall i :: 0 <= i < |result| ==>
        forall j :: 0 <= j < |result[i]| ==>
            result[i][j] == m[i][|m[i]|-1-j]
    // Row preservation: each row contains the same elements
    ensures forall i :: 0 <= i < |result| ==>
        SameElements(result[i], m[i])
    // Dimensions are preserved
    ensures forall i :: 0 <= i < |result| ==>
        |result[i]| == |m[i]|
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
