Two players take turns picking cards from either end of a row of n cards. Each card has a distinct
integer value. The first player (Sereja) goes first. Both players use a greedy strategy: they always
choose the card with the larger value between the leftmost and rightmost available cards. Determine
the final scores of both players.

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

lemma prove_sereja_score_nonnegative(cards: seq<int>, left: int, right: int, sereja_turn: bool)
  requires 0 <= left <= right < |cards|
  requires forall i :: 0 <= i < |cards| ==> cards[i] > 0
  ensures sereja_optimal_score(cards, left, right, sereja_turn) >= 0
  decreases right - left + 1
{
  if left == right {
    // Base case: single card
  } else if cards[left] > cards[right] {
    prove_sereja_score_nonnegative(cards, left+1, right, !sereja_turn);
  } else {
    prove_sereja_score_nonnegative(cards, left, right-1, !sereja_turn);
  }
}

lemma prove_sereja_score_bounded(cards: seq<int>, left: int, right: int, sereja_turn: bool)
  requires 0 <= left <= right < |cards|
  requires forall i :: 0 <= i < |cards| ==> cards[i] > 0
  ensures sereja_optimal_score(cards, left, right, sereja_turn) <= sum(cards[left..right+1])
  decreases right - left + 1
{
  if left == right {
    // Base case
  } else if cards[left] > cards[right] {
    prove_sereja_score_bounded(cards, left+1, right, !sereja_turn);
    prove_sum_split_left(cards, left, right);
  } else {
    prove_sereja_score_bounded(cards, left, right-1, !sereja_turn);
    prove_sum_split_right(cards, left, right);
  }
}

lemma prove_sum_slice_equivalence(cards: seq<int>)
  requires |cards| >= 1
  ensures sum(cards[0..|cards|]) == sum(cards)
{
  assert cards[0..|cards|] == cards;
}

lemma prove_sum_split_left(cards: seq<int>, left: int, right: int)
  requires 0 <= left <= right < |cards|
  ensures sum(cards[left..right+1]) == cards[left] + sum(cards[left+1..right+1])
{
  if left == right {
    assert cards[left..right+1] == [cards[left]];
    assert cards[left+1..right+1] == [];
  } else {
    assert cards[left..right+1] == [cards[left]] + cards[left+1..right+1];
  }
}

lemma prove_sum_split_right(cards: seq<int>, left: int, right: int)
  requires 0 <= left <= right < |cards|
  ensures sum(cards[left..right+1]) == sum(cards[left..right]) + cards[right]
{
  if left == right {
    assert cards[left..right] == [];
    assert cards[left..right+1] == [cards[right]];
  } else {
    assert cards[left..right+1] == cards[left..right] + [cards[right]];
    prove_sum_append(cards[left..right], cards[right]);
  }
}

lemma prove_sum_append(s: seq<int>, x: int)
  ensures sum(s + [x]) == sum(s) + x
{
  if |s| == 0 {
    assert s + [x] == [x];
  } else {
    assert s + [x] == [s[0]] + (s[1..] + [x]);
    prove_sum_append(s[1..], x);
  }
}

method solve(cards: seq<int>) returns (scores: seq<int>)
  requires ValidInput(cards)
  ensures ValidOutput(scores, cards)
{
  var sereja_score := sereja_optimal_score(cards, 0, |cards|-1, true);
  var dima_score := sum(cards) - sereja_score;

  assert sereja_score >= 0 by { prove_sereja_score_nonnegative(cards, 0, |cards|-1, true); }
  prove_sereja_score_bounded(cards, 0, |cards|-1, true);
  prove_sum_slice_equivalence(cards);
  assert sereja_score <= sum(cards);
  assert dima_score >= 0;

  scores := [sereja_score, dima_score];
}
