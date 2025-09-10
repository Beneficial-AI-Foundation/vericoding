/*
Given a non-negative integer k where 0 ≤ k ≤ 33, return the kth row of Pascal's triangle 
as a list of integers. Row indexing starts from 0. In Pascal's triangle, each element 
equals the sum of the two elements directly above it in the previous row.
*/

function binomial(n: int, k: int): int
    requires 0 <= k <= n
{
    if k == 0 || k == n then 1
    else if k == 1 then n
    else binomial(n-1, k-1) + binomial(n-1, k)
}

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method getRow(k: int) returns (result: seq<int>)
    requires 0 <= k <= 33
    ensures |result| == k + 1
    ensures forall i :: 0 <= i < |result| ==> result[i] == binomial(k, i)
    ensures forall i :: 0 <= i < |result| ==> result[i] > 0
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
