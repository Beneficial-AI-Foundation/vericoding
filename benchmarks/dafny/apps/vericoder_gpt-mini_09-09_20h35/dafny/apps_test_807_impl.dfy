predicate ValidInput(n: int, c: int, prices: seq<int>) {
    n >= 2 && |prices| == n && c >= 0 &&
    (forall i :: 0 <= i < |prices| ==> prices[i] >= 0)
}

function ProfitForDay(prices: seq<int>, day: int, c: int): int
    requires 0 <= day < |prices| - 1
{
    prices[day] - prices[day + 1] - c
}

function MaxPossibleProfit(prices: seq<int>, c: int): int
    requires |prices| >= 2
{
    var profits := seq(|prices| - 1, i requires 0 <= i < |prices| - 1 => ProfitForDay(prices, i, c));
    if |profits| == 0 then 0 else
    var maxProfit := profits[0];
    if |profits| == 1 then maxProfit else
    seq_max(profits)
}

function seq_max(s: seq<int>): int
    requires |s| > 0
{
    if |s| == 1 then s[0]
    else if s[0] >= seq_max(s[1..]) then s[0]
    else seq_max(s[1..])
}

predicate CorrectResult(n: int, c: int, prices: seq<int>, result: int) {
    ValidInput(n, c, prices) ==>
    (result >= 0 &&
     (result == 0 <==> (forall i :: 0 <= i < n - 1 ==> ProfitForDay(prices, i, c) <= 0)) &&
     (result > 0 ==> (exists i :: 0 <= i < n - 1 && ProfitForDay(prices, i, c) == result)) &&
     (forall i :: 0 <= i < n - 1 ==> ProfitForDay(prices, i, c) <= result))
}

// <vc-helpers>
lemma seq_max_nonempty_ge_all(s: seq<int>)
    requires |s| > 0
    ensures forall i :: 0 <= i < |s| ==> s[i] <= seq_max(s)
    ensures exists i :: 0 <= i < |s| && s[i] == seq_max(s)
  decreases |s|
{
  if |s| == 1 {
    // seq_max(s) == s[0] by definition
    assert forall i :: 0 <= i < |s| ==> s[i] <= seq_max(s);
    assert exists i :: 0 <= i < |s| && s[i] == seq_max(s);
  } else {
    var tail := s[1..];
    // Inductive hypothesis for tail
    seq_max_nonempty_ge_all(tail);
    var m_tail := seq_max(tail);

    if s[0] >= m_tail {
      // By definition seq_max(s) == s[0]
      assert seq_max(s) == s[0];
      // head <= seq_max(s)
      assert s[0] <= seq_max(s);
      // tail elements <= m_tail and m_tail <= s[0] == seq_max(s)
      assert forall i :: 0 <= i < |tail| ==> tail[i] <= m_tail;
      assert m_tail <= s[0];
      // combine to get tail[i] <= seq_max(s)
      assert forall j :: 0 <= j < |s| ==>
        if j == 0 then s[j] <= seq_max(s) else tail[j - 1] <= seq_max(s);
      // existence: head equals seq_max(s)
      assert exists i :: 0 <= i < |s| && s[i] == seq_max(s);
    } else {
      // By definition seq_max(s) == m_tail
      assert seq_max(s) == m_tail;
      // tail elements <= seq_max(s)
      assert forall i :: 0 <= i < |tail| ==> tail[i] <= seq_max(s);
      // head <= m_tail == seq_max(s) because otherwise we would be in the other branch
      assert s[0] <= seq_max(s);
      // combine to get all elements <= seq_max(s)
      assert forall j :: 0 <= j < |s| ==>
        if j == 0 then s[j] <= seq_max(s) else tail[j - 1] <= seq_max(s);
      // existence: from tail existence, shift index by 1
      assert (exists k :: 0 <= k < |tail| && tail[k] == m_tail);
      // construct existence for original sequence
      assert exists i :: 0 <= i < |s| && s[i] == seq_max(s);
    }
  }
}

lemma MaxPossibleProfit_is_seqmax(prices: seq<int>, c: int)
    requires |prices| >= 2
    ensures MaxPossibleProfit(prices, c) == seq_max(seq(|prices| - 1, i => ProfitForDay(prices, i, c)))
{
  var profits := seq(|prices| - 1, i => ProfitForDay(prices, i, c));
  // Given |prices| >= 2, we have |profits| = |prices| - 1 >= 1
  if |profits| == 1 {
    // MaxPossibleProfit returns profits[0] and seq_max(profits) = profits[0]
    assert MaxPossibleProfit(prices, c) == profits[0];
    assert seq_max(profits) == profits[0];
    assert MaxPossibleProfit(prices, c) == seq_max(profits);
  } else {
    // |profits| >= 2, by definition MaxPossibleProfit returns seq_max(profits)
    assert MaxPossibleProfit(prices, c) == seq_max(profits);
  }
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, c: int, prices: seq<int>) returns (result: int)
    requires ValidInput(n, c, prices)
    ensures CorrectResult(n, c, prices, result)
// </vc-spec>
// <vc-code>
{
  // Relate n and prices length
  assert |prices| == n;

  var mp := MaxPossibleProfit(prices, c);
  var profits := seq(|prices| - 1, i => ProfitForDay(prices, i, c));
  // Relate mp to seq_max(profits)
  MaxPossibleProfit_is_seqmax(prices, c);
  assert mp == seq_max(profits);

  // profits is non-empty because |prices| >= 2
  assert |profits| > 0;
  seq_max_nonempty_ge_all(profits);

  if mp > 0 {
    result := mp;
    // existence of index with maximum profit
    assert exists i :: 0 <= i < |profits| && profits[i] == seq_max(profits);
    // translate to ProfitForDay and range n-1
    assert exists i :: 0 <= i < n - 1 && ProfitForDay(prices, i, c) == result;
    // all profits <= result
    assert forall i :: 0 <= i < n - 1 ==> ProfitForDay(prices, i, c) <= result;
    // not all profits <= 0 (since some equals result > 0)
    assert !(forall i :: 0 <= i < n - 1 ==> ProfitForDay(prices, i, c) <= 0);
  } else {
    // mp <= 0
    result := 0;
    // seq_max(profits) == mp <= 0
    assert seq_max(profits) <= 0;
    // all profits <= seq_max(profits)
    assert forall i :: 0 <= i < n - 1 ==> profits[i] <= seq_max(profits);
    // combine to get all profits <= result (0)
    assert forall i :: 0 <= i < n - 1 ==> ProfitForDay(prices, i, c) <= result;
    // if all profits <= 0 then result == 0 (result already 0)
    assert (forall i :: 0 <= i < n - 1 ==> ProfitForDay(prices, i, c) <= 0) ==> result == 0;
  }

  // result >= 0 holds in both branches
  assert result >= 0;
}
// </vc-code>

