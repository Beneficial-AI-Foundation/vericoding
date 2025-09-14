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
predicate ValidInput(cards: seq<int>)
{
    |cards| == 5 && forall i :: 0 <= i < |cards| ==> cards[i] > 0
}

function sum(s: seq<int>): int
  decreases |s|
{ if s == [] then 0 else s[0] + sum(s[1..]) }

function findMax(s: seq<int>): int
  requires s != []
  decreases |s|
{ if |s| ==1 then s[0] else if (s[0] > findMax(s[1..])) then s[0] else findMax(s[1..]) }

function minPossibleSum(cards: seq<int>): int
  requires ValidInput(cards)
  ensures minPossibleSum(cards) >= 0
  ensures minPossibleSum(cards) <= sum(cards)
{ sum(cards) - findMax(cards) + 1 }
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
  result := sum(cards) - findMax(cards) + 1;
}
// </vc-code>

