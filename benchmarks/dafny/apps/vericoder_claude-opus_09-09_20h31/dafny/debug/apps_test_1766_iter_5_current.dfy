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
lemma sum_bounds(cards: seq<int>)
  requires |cards| >= 1
  requires forall i :: 0 <= i < |cards| ==> cards[i] > 0
  ensures sum(cards) > 0
{
  if |cards| == 1 {
    assert sum(cards) == cards[0];
    assert cards[0] > 0;
  } else {
    assert cards[0] > 0;
    sum_bounds(cards[1..]);
    assert sum(cards[1..]) > 0;
    assert sum(cards) == cards[0] + sum(cards[1..]);
  }
}

lemma sum_split_left(cards: seq<int>, left: int, right: int)
  requires 0 <= left < right < |cards|
  ensures sum(cards[left..right+1]) == cards[left] + sum(cards[left+1..right+1])
{
  assert cards[left..right+1] == [cards[left]] + cards[left+1..right+1];
}

lemma sum_split_right(cards: seq<int>, left: int, right: int)
  requires 0 <= left < right < |cards|
  ensures sum(cards[left..right+1]) == sum(cards[left..right]) + cards[right]
{
  var s := cards[left..right+1];
  var s_prefix := cards[left..right];
  assert s == s_prefix + [cards[right]];
  
  calc == {
    sum(s);
    sum(s_prefix + [cards[right]]);
    { sum_append(s_prefix, [cards[right]]); }
    sum(s_prefix) + sum([cards[right]]);
    sum(s_prefix) + cards[right];
    sum(cards[left..right]) + cards[right];
  }
}

lemma sum_append(s1: seq<int>, s2: seq<int>)
  ensures sum(s1 + s2) == sum(s1) + sum(s2)
{
  if |s1| == 0 {
    assert s1 + s2 == s2;
  } else {
    assert s1 == [s1[0]] + s1[1..];  // Help Dafny understand the decomposition
    calc == {
      sum(s1 + s2);
      { assert s1 + s2 == [s1[0]] + s1[1..] + s2; }
      sum([s1[0]] + s1[1..] + s2);
      { assert [s1[0]] + s1[1..] + s2 == [s1[0]] + (s1[1..] + s2); }
      sum([s1[0]] + (s1[1..] + s2));
      s1[0] + sum(s1[1..] + s2);
      { sum_append(s1[1..], s2); }
      s1[0] + sum(s1[1..]) + sum(s2);
      sum(s1) + sum(s2);
    }
  }
}

lemma sereja_score_bounds(cards: seq<int>, left: int, right: int, sereja_turn: bool)
  requires 0 <= left <= right < |cards|
  requires forall i :: 0 <= i < |cards| ==> cards[i] > 0
  ensures 0 <= sereja_optimal_score(cards, left, right, sereja_turn) <= sum(cards[left..right+1])
  decreases right - left + 1
{
  if left == right {
    if sereja_turn {
      assert sereja_optimal_score(cards, left, right, sereja_turn) == cards[left];
      assert cards[left..right+1] == [cards[left]];
      assert sum(cards[left..right+1]) == cards[left];
    } else {
      assert sereja_optimal_score(cards, left, right, sereja_turn) == 0;
      assert cards[left] > 0;
      assert sum(cards[left..right+1]) == cards[left] > 0;
    }
  } else if cards[left] > cards[right] {
    sereja_score_bounds(cards, left+1, right, !sereja_turn);
    var next_score := sereja_optimal_score(cards, left+1, right, !sereja_turn);
    assert 0 <= next_score <= sum(cards[left+1..right+1]);
    
    if sereja_turn {
      sum_split_left(cards, left, right);
      assert sum(cards[left..right+1]) == cards[left] + sum(cards[left+1..right+1]);
      assert sereja_optimal_score(cards, left, right, sereja_turn) == cards[left] + next_score;
      assert cards[left] > 0;
      assert sereja_optimal_score(cards, left, right, sereja_turn) >= cards[left] + 0 >= 0;
      assert sereja_optimal_score(cards, left, right, sereja_turn) <= cards[left] + sum(cards[left+1..right+1]);
      assert sereja_optimal_score(cards, left, right, sereja_turn) <= sum(cards[left..right+1]);
    } else {
      assert sereja_optimal_score(cards, left, right, sereja_turn) == 0 + next_score;
      assert 0 <= sereja_optimal_score(cards, left, right, sereja_turn) <= sum(cards[left+1..right+1]);
      sum_split_left(cards, left, right);
      assert sum(cards[left+1..right+1]) < sum(cards[left..right+1]);
    }
  } else {
    sereja_score_bounds(cards, left, right-1, !sereja_turn);
    var next_score := sereja_optimal_score(cards, left, right-1, !sereja_turn);
    assert 0 <= next_score <= sum(cards[left..right]);
    
    if sereja_turn {
      sum_split_right(cards, left, right);
      assert sum(cards[left..right+1]) == sum(cards[left..right]) + cards[right];
      assert sereja_optimal_score(cards, left, right, sereja_turn) == cards[right] + next_score;
      assert cards[right] > 0;
      assert sereja_optimal_score(cards, left, right, sereja_turn) >= cards[right] + 0 >= 0;
      assert sereja_optimal_score(cards, left, right, sereja_turn) <= cards[right] + sum(cards[left..right]);
      assert sereja_optimal_score(cards, left, right, sereja_turn) <= sum(cards[left..right+1]);
    } else {
      assert sereja_optimal_score(cards, left, right, sereja_turn) == 0 + next_score;
      assert 0 <= sereja_optimal_score(cards, left, right, sereja_turn) <= sum(cards[left..right]);
      sum_split_right(cards, left, right);
      assert sum(cards[left..right]) < sum(cards[left..right+1]);
    }
  }
}

lemma optimal_score_non_negative(cards: seq<int>)
  requires ValidInput(cards)
  ensures sereja_optimal_score(cards, 0, |cards|-1, true) >= 0
{
  sereja_score_bounds(cards, 0, |cards|-1, true);
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
  
  sereja_score_bounds(cards, 0, |cards|-1, true);
  assert cards[0..|cards|-1+1] == cards;
  
  var total := sum(cards);
  sum_bounds(cards);
  assert total > 0;
  assert 0 <= sereja_score <= total;
  
  var dima_score := total - sereja_score;
  assert dima_score >= 0;
  
  scores := [sereja_score, dima_score];
  assert scores[0] == sereja_score >= 0;
  assert scores[1] == dima_score >= 0;
  assert scores[0] + scores[1] == total;
}
// </vc-code>

