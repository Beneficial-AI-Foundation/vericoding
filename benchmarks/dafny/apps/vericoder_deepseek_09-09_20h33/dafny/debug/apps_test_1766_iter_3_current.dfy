predicate ValidInput(cards: seq<int>)
{
  |cards| >= 1 &&
  (forall i :: 0 <= i < |cards| ==> cards[i] > 0) &&
  (forall i, j :: 0 <= i < j < |cards| ==> cards[i] != cards[j])
}

function sum(cards: seq<int>): int
{
  if |cards| == 0 then 0
  else cards[0] + sum(cards[1..])
}

function sereja_optimal_score(cards: seq<int>, left: int, right: int, sereja_turn: bool): int
  requires 0 <= left <= right < |cards|
  decreases right - left + 1
{
  if left == right then
    if sereja_turn then cards[left] else 0
  else if cards[left] > cards[right] then
    (if sereja_turn then cards[left] else 0) + sereja_optimal_score(cards, left+1, right, !sereja_turn)
  else
    (if sereja_turn then cards[right] else 0) + sereja_optimal_score(cards, left, right-1, !sereja_turn)
}

predicate ValidOutput(scores: seq<int>, cards: seq<int>)
  requires ValidInput(cards)
{
  |scores| == 2 &&
  scores[0] >= 0 && scores[1] >= 0 &&
  scores[0] + scores[1] == sum(cards) &&
  scores[0] == sereja_optimal_score(cards, 0, |cards|-1, true) &&
  scores[1] == sum(cards) - sereja_optimal_score(cards, 0, |cards|-1, true)
}

// <vc-helpers>
lemma sereja_lemma(cards: seq<int>, left: int, right: int, sereja_turn: bool)
  requires 0 <= left <= right < |cards|
  ensures sereja_optimal_score(cards, left, right, sereja_turn) + sereja_optimal_score(cards, left, right, !sereja_turn) == sum(cards[left..right+1])
  decreases right - left + 1
{
  if left == right {
    // Base case: single card
    if sereja_turn {
      assert sereja_optimal_score(cards, left, right, true) == cards[left];
      assert sereja_optimal_score(cards, left, right, false) == 0;
    } else {
      assert sereja_optimal_score(cards, left, right, false) == 0;
      assert sereja_optimal_score(cards, left, right, true) == cards[left];
    }
  } else {
    var sub := cards[left..right+1];
    assert |sub| > 0;
    if cards[left] > cards[right] {
      // Left card is better
      sereja_lemma(cards, left+1, right, !sereja_turn);
      calc {
        sereja_optimal_score(cards, left, right, sereja_turn) + sereja_optimal_score(cards, left, right, !sereja_turn);
      ==
        (if sereja_turn then cards[left] else 0) + sereja_optimal_score(cards, left+1, right, !sereja_turn) +
        (if !sereja_turn then cards[left] else 0) + sereja_optimal_score(cards, left+1, right, sereja_turn);
      ==
        (if sereja_turn then cards[left] else 0) + (if !sereja_turn then cards[left] else 0) + 
        sereja_optimal_score(cards, left+1, right, !sereja_turn) + sereja_optimal_score(cards, left+1, right, sereja_turn);
      ==
        cards[left] + sum(cards[left+1..right+1]);
      ==
        { assert cards[left..right+1] == [cards[left]] + cards[left+1..right+1]; }
        sum(cards[left..right+1]);
      }
    } else {
      // Right card is better
      sereja_lemma(cards, left, right-1, !sereja_turn);
      calc {
        sereja_optimal_score(cards, left, right, sereja_turn) + sereja_optimal_score(cards, left, right, !sereja_turn);
      ==
        (if sereja_turn then cards[right] else 0) + sereja_optimal_score(cards, left, right-1, !sereja_turn) +
        (if !sereja_turn then cards[right] else 0) + sereja_optimal_score(cards, left, right-1, sereja_turn);
      ==
        (if sereja_turn then cards[right] else 0) + (if !sereja_turn then cards[right] else 0) + 
        sereja_optimal_score(cards, left, right-1, !sereja_turn) + sereja_optimal_score(cards, left, right-1, sereja_turn);
      ==
        cards[right] + sum(cards[left..right]);
      ==
        { assert cards[left..right+1] == cards[left..right] + [cards[right]]; }
        sum(cards[left..right+1]);
      }
    }
  }
}
// </vc-helpers>

// <vc-spec>
method solve(cards: seq<int>) returns (scores: seq<int>)
  requires ValidInput(cards)
  ensures ValidOutput(scores, cards)
// </vc-spec>
// <vc-code>
{
  var n := |cards|;
  sereja_lemma(cards, 0, n-1, true);
  scores := [sereja_optimal_score(cards, 0, n-1, true), sum(cards) - sereja_optimal_score(cards, 0, n-1, true)];
}
// </vc-code>

