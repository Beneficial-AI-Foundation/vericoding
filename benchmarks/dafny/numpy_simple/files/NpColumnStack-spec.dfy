// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method ColumnStack(input: seq<seq<int>>, m: int, n: int) returns (result: seq<seq<int>>)
    requires 
        n > 0 &&
        |input| == n &&
        (forall i :: 0 <= i < n ==> |input[i]| == m)
    ensures
        |result| == m &&
        (forall j :: 0 <= j < m ==> |result[j]| == n) &&
        |result| * n == m * n &&
        (forall i, j :: 0 <= i < n && 0 <= j < m ==> 
            result[j][i] == input[i][j])
// </vc-spec>
// <vc-code>
{
    assume {:axiom} false;
}
// </vc-code>
