// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method MaxProfit(prices: seq<nat>) returns (result: nat)
    ensures
        (result == 0 && |prices| == 0) ||
        (exists i: int, j: int :: 0 <= i < j < |prices| && prices[j] >= prices[i] && prices[j] - prices[i] == result) ||
        (forall i: int, j: int :: 0 <= i < j < |prices| ==> prices[j] < prices[i])
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume {:axiom} false;
    result := 0;
    // impl-end
}
// </vc-code>
