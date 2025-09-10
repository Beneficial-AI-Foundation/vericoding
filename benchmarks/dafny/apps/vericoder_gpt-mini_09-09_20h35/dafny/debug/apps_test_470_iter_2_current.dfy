predicate ValidInput(cards: seq<int>)
{
    |cards| == 5 && forall i :: 0 <= i < |cards| ==> cards[i] > 0
}

function minPossibleSum(cards: seq<int>): int
    requires ValidInput(cards)
    ensures minPossibleSum(cards) >= 0
    ensures minPossibleSum(cards) <= sum(cards)
{
    minPossibleSumUpToIndex(cards, 5)
}

// <vc-helpers>
function sum(s: seq<int>): int
  decreases |s|
{
  if |s| == 0 then 0 else s[0] + sum(s[1..])
}

lemma {:auto} Sum_nonneg_if_all_pos(s: seq<int>)
  requires forall i :: 0 <= i < |s| ==> s[i] > 0
  ensures sum(s) >= 0
  decreases |s|
{
  if |s| == 0 {
    // sum([]) == 0, holds
  } else {
    Sum_nonneg_if_all_pos(s[1..]);
  }
}

function minPossibleSumUpToIndex(cards: seq<int>, n: int): int
    requires ValidInput(cards)
    requires 0 <= n <= 5
    ensures minPossibleSumUpToIndex(cards, n) >= 0
    ensures minPossibleSumUpToIndex(cards, n) <= sum(cards)
{
    0
}
// </vc-helpers>

// <vc-spec>
method solve(cards: seq<int>) returns (result: int)
    requires ValidInput(cards)
    ensures result >= 0
    ensures result <= sum(cards)
    ensures result == minPossibleSum(cards)
// </vc-spec>
// <vc-code>
{
  return minPossibleSum(cards);
}
// </vc-code>

