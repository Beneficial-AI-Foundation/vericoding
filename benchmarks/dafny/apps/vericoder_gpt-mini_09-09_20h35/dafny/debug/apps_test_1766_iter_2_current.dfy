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
lemma sum_range_nonneg(cards: seq<int>, left: int, right: int)
  requires ValidInput(cards)
  requires 0 <= left <= right < |cards|
  ensures 0 <= sum(cards[left..right+1])
  decreases right - left + 1
{
  if left == right {
    // sum of single positive card is positive
    assert sum(cards[left..right+1]) == cards[left];
    assert cards[left] > 0;
  } else {
    // sum(cards[left..right+1]) == cards[left] + sum(cards[left+1..right+1])
    assert sum(cards[left..right+1]) == cards[left] + sum(cards[left+1..right+1]);
    // cards[left] > 0
    assert cards[left] > 0;
    // recursive call on smaller range
    sum_range_nonneg(cards, left+1, right);
    // conclude positivity
    assert sum(cards[left+1..right+1]) >= 0;
  }
}

lemma sereja_score_nonneg(cards: seq<int>, left: int, right: int, sereja_turn: bool)
  requires ValidInput(cards)
  requires 0 <= left <= right < |cards|
  ensures 0 <= sereja_optimal_score(cards, left, right, sereja_turn)
  decreases right - left + 1
{
  if left == right {
    if sereja_turn {
      assert sereja_optimal_score(cards, left, right, sereja_turn) == cards[left];
      assert cards[left] > 0;
    } else {
      assert sereja_optimal_score(cards, left, right, sereja_turn) == 0;
    }
  } else {
    if cards[left] > cards[right] {
      if sereja_turn {
        // sereja_optimal_score = cards[left] + sereja_optimal_score(cards, left+1, right, !sereja_turn)
        sereja_score_nonneg(cards, left+1, right, !sereja_turn);
        assert sereja_optimal_score(cards, left+1, right, !sereja_turn) >= 0;
        assert cards[left] > 0;
      } else {
        // sereja_optimal_score = sereja_optimal_score(cards, left+1, right, !sereja_turn)
        sereja_score_nonneg(cards, left+1, right, !sereja_turn);
      }
    } else {
      if sereja_turn {
        // sereja_optimal_score = cards[right] + sereja_optimal_score(cards, left, right-1, !sereja_turn)
        sereja_score_nonneg(cards, left, right-1, !sereja_turn);
        assert sereja_optimal_score(cards, left, right-1, !sereja_turn) >= 0;
        assert cards[right] > 0;
      } else {
        // sereja_optimal_score = sereja_optimal_score(cards, left, right-1, !sereja_turn)
        sereja_score_nonneg(cards, left, right-1, !sereja_turn);
      }
    }
  }
}

lemma sereja_score_le_range(cards: seq<int>, left: int, right: int, sereja_turn: bool)
  requires ValidInput(cards)
  requires 0 <= left <= right < |cards|
  ensures sereja_optimal_score(cards, left, right, sereja_turn) <= sum(cards[left..right+1])
  decreases right - left + 1
{
  if left == right {
    if sereja_turn {
      assert sereja_optimal_score(cards, left, right, sereja_turn) == cards[left];
      assert sum(cards[left..right+1]) == cards[left];
    } else {
      assert sereja_optimal_score(cards, left, right, sereja_turn) == 0;
      assert sum(cards[left..right+1]) == cards[left];
      assert 0 <= sum(cards[left..right+1]);
    }
  } else {
    if cards[left] > cards[right] {
      if sereja_turn {
        // s = cards[left] + sereja_optimal_score(cards, left+1, right, !sereja_turn)
        sereja_score_le_range(cards, left+1, right, !sereja_turn);
        // sum(cards[left..right+1]) == cards[left] + sum(cards[left+1..right+1])
        assert sum(cards[left..right+1]) == cards[left] + sum(cards[left+1..right+1]);
        // by inductive hypothesis, remainder <= sum(cards[left+1..right+1])
        assert sereja_optimal_score(cards, left+1, right, !sereja_turn) <= sum(cards[left+1..right+1]);
        // hence s <= sum(cards[left..right+1])
      } else {
        // s = sereja_optimal_score(cards, left+1, right, !sereja_turn)
        sereja_score_le_range(cards, left+1, right, !sereja_turn);
        // sum(cards[left+1..right+1]) <= sum(cards[left..right+1])
        assert sum(cards[left..right+1]) == cards[left] + sum(cards[left+1..right+1]);
        assert sum(cards[left+1..right+1]) <= sum(cards[left..right+1]);
      }
    } else {
      if sereja_turn {
        // s = cards[right] + sereja_optimal_score(cards, left, right-1, !sereja_turn)
        sereja_score_le_range(cards, left, right-1, !sereja_turn);
        assert sum(cards[left..right+1]) == sum(cards[left..right]) + cards[right];
        assert sereja_optimal_score(cards, left, right-1, !sereja_turn) <= sum(cards[left..right]);
      } else {
        // s = sereja_optimal_score(cards, left, right-1, !sereja_turn)
        sereja_score_le_range(cards, left, right-1, !sereja_turn);
        assert sum(cards[left..right]) <= sum(cards[left..right+1]);
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
  var s := sereja_optimal_score(cards, 0, |cards|-1, true);
  var t := sum(cards) - s;
  // prove non-negativity of s and t to satisfy postconditions
  sereja_score_nonneg(cards, 0, |cards|-1, true);
  sereja_score_le_range(cards, 0, |cards|-1, true);
  assert s >= 0;
  assert t >= 0;
  scores := [s, t];
}
// </vc-code>

