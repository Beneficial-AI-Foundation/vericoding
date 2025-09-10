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
lemma SumLast(s: seq<int>)
  requires |s| > 0
  ensures sum(s) == sum(s[0..|s|-1]) + s[|s|-1]
  decreases |s|
{
  if |s| == 1 {
  } else {
    SumLast(s[1..]);
    var tail := s[1..];
    assert sum(tail) == sum(tail[0..|tail|-1]) + tail[|tail|-1];
    var prefix := s[0..|s|-1];
    var last := s[|s|-1];
    assert prefix == [s[0]] + s[1..|s|-1];
    assert s == [s[0]] + tail;
    assert sum(s) == s[0] + sum(tail);
    assert sum(tail) == sum(s[1..|s|-1]) + s[|s|-1];
    assert sum(prefix) == s[0] + sum(s[1..|s|-1]);
    assert sum(prefix) + last == s[0] + sum(s[1..|s|-1]) + s[|s|-1];
  }
}

lemma SumOfScores(cards: seq<int>, left: int, right: int)
  requires 0 <= left <= right < |cards| && ValidInput(cards)
  ensures sereja_optimal_score(cards, left, right, true) + sereja_optimal_score(cards, left, right, false) == sum(cards[left..right+1])
  decreases right - left
{
  if left == right {
    assert sum(cards[left..right+1]) == cards[left];
    assert sereja_optimal_score(cards, left, right, true) == cards[left];
    assert sereja_optimal_score(cards, left, right, false) == 0;
  } else {
    if cards[left] > cards[right] {
      SumOfScores(cards, left+1, right);
      var opt_sereja_true := sereja_optimal_score(cards, left, right, true);
      var opt_sereja_false := sereja_optimal_score(cards, left, right, false);
      var rec_sereja_true := sereja_optimal_score(cards, left+1, right, true);
      var rec_sereja_false := sereja_optimal_score(cards, left+1, right, false);
      assert opt_sereja_true == cards[left] + rec_sereja_false;
      assert opt_sereja_false == rec_sereja_true;
      assert rec_sereja_true + rec_sereja_false == sum(cards[left+1..right+1]);
      SumLast(cards[left+1..right+1]);
      assert opt_sereja_true + opt_sereja_false == cards[left] + (rec_sereja_true + rec_sereja_false) == cards[left] + sum(cards[left+1..right+1]);
      SumLast(cards[left..right+1]);
    } else {
      SumOfScores(cards, left, right-1);
      var opt_sereja_true := sereja_optimal_score(cards, left, right, true);
      var opt_sereja_false := sereja_optimal_score(cards, left, right, false);
      var rec_sereja_true := sereja_optimal_score(cards, left, right-1, true);
      var rec_sereja_false := sereja_optimal_score(cards, left, right-1, false);
      assert opt_sereja_true == cards[right] + rec_sereja_false;
      assert opt_sereja_false == rec_sereja_true;
      assert rec_sereja_true + rec_sereja_false == sum(cards[left..right]);
      SumLast(cards[left..right+1]);
      assert opt_sereja_true + opt_sereja_false == cards[right] + (rec_sereja_true + rec_sereja_false) == cards[right] + sum(cards[left..right]);
    }
  }
}

lemma SerejaScoreNonNegative(cards: seq<int>, left: int, right: int, sereja_turn: bool)
  requires 0 <= left <= right < |cards| && ValidInput(cards)
  ensures sereja_optimal_score(cards, left, right, sereja_turn) >= 0
  decreases right - left
{
  if left != right {
    if cards[left] > cards[right] {
      SerejaScoreNonNegative(cards, left+1, right, !sereja_turn);
    } else {
      SerejaScoreNonNegative(cards, left, right-1, !sereja_turn);
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
  SumOfScores(cards, 0, |cards|-1);
  SerejaScoreNonNegative(cards, 0, |cards|-1, true);
  SerejaScoreNonNegative(cards, 0, |cards|-1, false);
  var sereja_score := sereja_optimal_score(cards, 0, |cards|-1, true);
  var total := sum(cards);
  assert sereja_score >= 0;
  assert sereja_score <= total;
  scores := [sereja_score, total - sereja_score];
}
// </vc-code>

