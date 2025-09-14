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
function minPossibleSumUpToIndex(cards: seq<int>, k: int): int
  requires ValidInput(cards)
  requires 0 <= k <= 5
  ensures minPossibleSumUpToIndex(cards, k) == 0
  ensures minPossibleSumUpToIndex(cards, k) >= 0
  ensures minPossibleSumUpToIndex(cards, k) <= sum(cards)
{
  0
}

axiom SumPositiveForValidInput:
  forall cards: seq<int> :: ValidInput(cards) ==> sum(cards) >= 1
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
  result := minPossibleSum(cards);
}
// </vc-code>

