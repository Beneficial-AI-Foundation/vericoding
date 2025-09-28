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
  if |prices| == 0 {
    result := 0;
  } else if exists i: int, j: int :: 0 <= i < j < |prices| && prices[j] >= prices[i] {
    var ii: int, jj: int :| 0 <= ii < jj < |prices| && prices[jj] >= prices[ii];
    result := prices[jj] - prices[ii];
  } else {
    result := 0;
    assert forall i: int, j: int :: 0 <= i < j < |prices| ==> prices[j] < prices[i];
  }
}
// </vc-code>
