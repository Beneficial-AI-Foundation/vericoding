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
  } else if cards[left] > cards[right] {
    // Left card is better
    sereja_lemma(cards, left+1, right, !sereja_turn);
  } else {
    // Right card is better
    sereja_lemma(cards, left, right-1, !sereja_turn);
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
  var left := 0;
  var right := n - 1;
  var sereja_turn := true;
  var s1 := 0;
  var s2 := 0;
  
  while left <= right
    invariant 0 <= left <= right + 1
    invariant right < n
    invariant left + (n - right - 1) <= n
  {
    if cards[left] > cards[right] {
      if sereja_turn {
        s1 := s1 + cards[left];
      } else {
        s2 := s2 + cards[left];
      }
      left := left + 1;
    } else {
      if sereja_turn {
        s1 := s1 + cards[right];
      } else {
        s2 := s2 + cards[right];
      }
      right := right - 1;
    }
    sereja_turn := !sereja_turn;
  }
  
  sereja_lemma(cards, 0, n-1, true);
  scores := [s1, s2];
}
// </vc-code>

