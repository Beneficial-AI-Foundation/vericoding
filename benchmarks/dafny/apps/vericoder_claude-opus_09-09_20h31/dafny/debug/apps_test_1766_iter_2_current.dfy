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

lemma sereja_score_bounds(cards: seq<int>, left: int, right: int, sereja_turn: bool)
  requires 0 <= left <= right < |cards|
  requires forall i :: 0 <= i < |cards| ==> cards[i] > 0
  ensures 0 <= sereja_optimal_score(cards, left, right, sereja_turn) <= sum(cards[left..right+1])
  decreases right - left + 1
{
  if left == right {
    if sereja_turn {
      assert sereja_optimal_score(cards, left, right, sereja_turn) == cards[left];
      assert sum(cards[left..right+1]) == sum([cards[left]]) == cards[left];
    } else {
      assert sereja_optimal_score(cards, left, right, sereja_turn) == 0;
    }
  } else if cards[left] > cards[right] {
    sereja_score_bounds(cards, left+1, right, !sereja_turn);
  } else {
    sereja_score_bounds(cards, left, right-1, !sereja_turn);
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
  var dp := new int[n, n];
  
  // Base case: single card
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant forall k :: 0 <= k < i ==> dp[k, k] == cards[k]
  {
    dp[i, i] := cards[i];
    i := i + 1;
  }
  
  // Fill the dp table for increasing lengths
  var length := 2;
  while length <= n
    invariant 2 <= length <= n + 1
    invariant forall l, r :: 0 <= l <= r < n && r - l + 1 < length ==>
      dp[l, r] == sereja_optimal_score(cards, l, r, true)
  {
    var left := 0;
    while left <= n - length
      invariant 0 <= left <= n - length + 1
      invariant forall l, r :: 0 <= l <= r < n && r - l + 1 < length ==>
        dp[l, r] == sereja_optimal_score(cards, l, r, true)
      invariant forall l :: 0 <= l < left ==> 
        dp[l, l + length - 1] == sereja_optimal_score(cards, l, l + length - 1, true)
    {
      var right := left + length - 1;
      
      if cards[left] > cards[right] {
        dp[left, right] := cards[left] + (if left + 1 <= right - 1 then dp[left + 1, right - 1] else 0);
      } else {
        dp[left, right] := cards[right] + (if left + 1 <= right - 1 then dp[left + 1, right - 1] else 0);
      }
      
      left := left + 1;
    }
    length := length + 1;
  }
  
  var sereja_score := dp[0, n - 1];
  var dima_score := sum(cards) - sereja_score;
  scores := [sereja_score, dima_score];
}
// </vc-code>

