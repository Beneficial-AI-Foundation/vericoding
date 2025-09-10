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
lemma sereja_optimal_score_bounds(cards: seq<int>, left: int, right: int, sereja_turn: bool)
  requires 0 <= left <= right < |cards|
  requires ValidInput(cards)
  ensures 0 <= sereja_optimal_score(cards, left, right, sereja_turn) <= sum(cards[left..right+1])
  decreases right - left + 1
{
  if left == right {
    if sereja_turn {
      assert sereja_optimal_score(cards, left, right, sereja_turn) == cards[left];
      assert sum(cards[left..right+1]) == cards[left];
    } else {
      assert sereja_optimal_score(cards, left, right, sereja_turn) == 0;
      assert sum(cards[left..right+1]) == cards[left] >= 0;
    }
  } else if cards[left] > cards[right] {
    sereja_optimal_score_bounds(cards, left+1, right, !sereja_turn);
    sum_slice_relation(cards, left, right);
    if sereja_turn {
      assert sereja_optimal_score(cards, left, right, sereja_turn) == cards[left] + sereja_optimal_score(cards, left+1, right, !sereja_turn);
      assert sereja_optimal_score(cards, left+1, right, !sereja_turn) >= 0;
      assert cards[left] > 0;
    } else {
      assert sereja_optimal_score(cards, left, right, sereja_turn) == sereja_optimal_score(cards, left+1, right, !sereja_turn);
    }
  } else {
    sereja_optimal_score_bounds(cards, left, right-1, !sereja_turn);
    sum_slice_relation(cards, left, right);
    if sereja_turn {
      assert sereja_optimal_score(cards, left, right, sereja_turn) == cards[right] + sereja_optimal_score(cards, left, right-1, !sereja_turn);
      assert sereja_optimal_score(cards, left, right-1, !sereja_turn) >= 0;
      assert cards[right] > 0;
    } else {
      assert sereja_optimal_score(cards, left, right, sereja_turn) == sereja_optimal_score(cards, left, right-1, !sereja_turn);
    }
  }
}

lemma sum_non_negative(cards: seq<int>)
  requires |cards| >= 0
  requires forall i :: 0 <= i < |cards| ==> cards[i] > 0
  ensures sum(cards) >= 0
{
  if |cards| == 0 {
    assert sum(cards) == 0;
  } else {
    assert cards[0] > 0;
    sum_non_negative(cards[1..]);
    assert sum(cards[1..]) >= 0;
  }
}

lemma sum_slice_relation(cards: seq<int>, left: int, right: int)
  requires 0 <= left <= right < |cards|
  requires forall i :: 0 <= i < |cards| ==> cards[i] > 0
  ensures left < right ==> sum(cards[left..right+1]) == cards[left] + sum(cards[left+1..right+1])
  ensures left < right ==> sum(cards[left..right+1]) == cards[right] + sum(cards[left..right])
{
  if left < right {
    assert cards[left..right+1] == [cards[left]] + cards[left+1..right+1];
    assert cards[left..right+1] == cards[left..right] + [cards[right]];
  }
}

function memo_sereja(cards: seq<int>, left: int, right: int, sereja_turn: bool): int
  requires 0 <= left <= right < |cards|
  decreases right - left + 1
{
  sereja_optimal_score(cards, left, right, sereja_turn)
}
// </vc-helpers>

// <vc-spec>
method solve(cards: seq<int>) returns (scores: seq<int>)
  requires ValidInput(cards)
  ensures ValidOutput(scores, cards)
// </vc-spec>
// <vc-code>
{
  var sereja_score := sereja_optimal_score(cards, 0, |cards|-1, true);
  var total_sum := sum(cards);
  var dima_score := total_sum - sereja_score;
  
  sereja_optimal_score_bounds(cards, 0, |cards|-1, true);
  sum_non_negative(cards);
  
  assert sereja_score >= 0;
  assert sereja_score <= total_sum;
  assert dima_score >= 0;
  
  scores := [sereja_score, dima_score];
}
// </vc-code>

