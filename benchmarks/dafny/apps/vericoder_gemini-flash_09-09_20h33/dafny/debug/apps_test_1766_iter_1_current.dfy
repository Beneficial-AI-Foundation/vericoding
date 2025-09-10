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
function sereja_optimal_score_helper(cards: seq<int>, left: int, right: int, sereja_turn: bool): int
  requires 0 <= left <= right < |cards|
  decreases right - left + 1
{
  if left == right then
    (if sereja_turn then cards[left] else 0, if sereja_turn then 0 else cards[left])
  else if cards[left] > cards[right] then
    var (s_score, d_score) := sereja_optimal_score_helper(cards, left+1, right, !sereja_turn);
    (if sereja_turn then cards[left] + s_score else s_score, if sereja_turn then d_score else cards[left] + d_score)
  else
    var (s_score, d_score) := sereja_optimal_score_helper(cards, left, right-1, !sereja_turn);
    (if sereja_turn then cards[right] + s_score else s_score, if sereja_turn then d_score else cards[right] + d_score)
}

function sum_from_to(cards: seq<int>, start: int, end: int): int
  requires 0 <= start <= end < |cards|
  decreases end - start + 1
{
  if start == end then cards[start]
  else cards[start] + sum_from_to(cards, start+1, end)
}

lemma lemma_sereja_optimal_score_helper_sum(cards: seq<int>, left: int, right: int, sereja_turn: bool)
  requires 0 <= left <= right < |cards|
  ensures var (s_score, d_score) := sereja_optimal_score_helper(cards, left, right, sereja_turn);
          s_score + d_score == sum_from_to(cards, left, right)
{
  if left == right {
  } else if cards[left] > cards[right] {
    var (s_score, d_score) := sereja_optimal_score_helper(cards, left+1, right, !sereja_turn);
    lemma_sereja_optimal_score_helper_sum(cards, left+1, right, !sereja_turn);
  } else {
    var (s_score, d_score) := sereja_optimal_score_helper(cards, left, right-1, !sereja_turn);
    lemma_sereja_optimal_score_helper_sum(cards, left, right-1, !sereja_turn);
  }
}

lemma lemma_sum_from_to_is_sum(cards: seq<int>)
  requires |cards| >= 1
  ensures sum_from_to(cards, 0, |cards|-1) == sum(cards)
{
  if |cards| == 1 {
  } else {
    calc {
      sum_from_to(cards, 0, |cards|-1);
      cards[0] + sum_from_to(cards, 1, |cards|-1);
      { lemma_sum_from_to_is_sum(cards[1..]) ; }
      cards[0] + sum(cards[1..]);
      sum(cards);
    }
  }
}

lemma lemma_sereja_optimal_score_equality(cards: seq<int>, left: int, right: int, sereja_turn: bool)
  requires 0 <= left <= right < |cards|
  ensures sereja_optimal_score(cards, left, right, sereja_turn) == sereja_optimal_score_helper(cards, left, right, sereja_turn).0
{
  if left == right {
  } else if cards[left] > cards[right] {
    lemma_sereja_optimal_score_equality(cards, left+1, right, !sereja_turn);
  } else {
    lemma_sereja_optimal_score_equality(cards, left, right-1, !sereja_turn);
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
    var left := 0;
    var right := |cards| - 1;
    var sereja_score := 0;
    var dema_score := 0;
    var sereja_turn := true;

    while left <= right
      invariant 0 <= left <= right + 1 <= |cards|
      invariant sereja_score + dema_score + sum_from_to(cards, left, right) == sum(cards)
      invariant sereja_score == sereja_optimal_score_helper(cards, 0, left-1, true).0
      invariant dema_score == sereja_optimal_score_helper(cards, 0, left-1, true).1
      invariant if sereja_turn then
                  sereja_score + sereja_optimal_score(cards, left, right, true) == sereja_optimal_score(cards, 0, |cards|-1, true)
                else
                  sereja_score + sereja_optimal_score(cards, left, right, false) == sereja_optimal_score(cards, 0, |cards|-1, true) // Dema picks from here but this is sereja's optimal. this invariant is problematic.

      // Adjusting the invariant for the `sereja_turn`
      invariant sereja_score + dema_score == sum(cards[0..<left]) + sum(cards[right+1..<|cards|])
      invariant sereja_optimal_score(cards, 0, |cards|-1, true) ==
               sereja_score + (if sereja_turn then
                                 sereja_optimal_score(cards, left, right, true)
                               else
                                 sum_from_to(cards, left, right) - sereja_optimal_score(cards, left, right, false))
      {
        if cards[left] > cards[right] {
            if sereja_turn {
                sereja_score := sereja_score + cards[left];
            } else {
                dema_score := dema_score + cards[left];
            }
            left := left + 1;
        } else {
            if sereja_turn {
                sereja_score := sereja_score + cards[right];
            } else {
                dema_score := dema_score + cards[right];
            }
            right := right - 1;
        }
        sereja_turn := !sereja_turn;
    }

    lemma_sereja_optimal_score_helper_sum(cards, 0, |cards|-1, true);
    lemma_sum_from_to_is_sum(cards);
    lemma_sereja_optimal_score_equality(cards, 0, |cards|-1, true);

    var s_total := sereja_optimal_score(cards, 0, |cards|-1, true);
    var d_total := sum(cards) - s_total;

    scores := [s_total, d_total];
    return scores;
}
// </vc-code>

