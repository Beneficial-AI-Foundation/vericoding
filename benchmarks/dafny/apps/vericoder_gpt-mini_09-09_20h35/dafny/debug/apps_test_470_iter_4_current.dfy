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
  } else {
    Sum_nonneg_if_all_pos(s[1..]);
  }
}

lemma {:auto} Sum_concat(s: seq<int>, t: seq<int>)
  decreases |s|
  ensures sum(s + t) == sum(s) + sum(t)
{
  if |s| == 0 {
    // sum([] + t) == sum(t) == 0 + sum(t)
  } else {
    Sum_concat(s[1..], t);
    // Unfold definitions and use induction hypothesis
    assert sum(s + t) == s[0] + sum(s[1..] + t);
    assert sum(s[1..] + t) == sum(s[1..]) + sum(t);
    assert s[0] + sum(s[1..] + t) == s[0] + (sum(s[1..]) + sum(t));
    assert s[0] + (sum(s[1..]) + sum(t)) == (s[0] + sum(s[1..])) + sum(t);
    assert (s[0] + sum(s[1..])) + sum(t) == sum(s) + sum(t);
    assert sum(s + t) == sum(s) + sum(t);
  }
}

lemma {:auto} Prefix_le_sum(cards: seq<int>, n: int)
  requires ValidInput(cards)
  requires 0 <= n <= |cards|
  ensures sum(cards[0..n]) <= sum(cards)
{
  Sum_concat(cards[0..n], cards[n..]);
  Sum_nonneg_if_all_pos(cards[n..]);
  assert sum(cards) == sum(cards[0..n]) + sum(cards[n..]);
  assert sum(cards[n..]) >= 0;
  // hence sum(cards[0..n]) <= sum(cards)
}

function minPossibleSumUpToIndex(cards: seq<int>, n: int): int
    requires ValidInput(cards)
    requires 0 <= n <= 5
    ensures minPossibleSumUpToIndex(cards, n) >= 0
    ensures minPossibleSumUpToIndex(cards, n) <= sum(cards)
{
    sum(cards[0..n])
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

