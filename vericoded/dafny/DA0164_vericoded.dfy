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

// </vc-helpers>

// <vc-spec>
method solve(n: int, c: int, prices: seq<int>) returns (result: int)
    requires ValidInput(n, c, prices)
    ensures CorrectResult(n, c, prices, result)
// </vc-spec>
// <vc-code>
{
  var i := 0;
  var maxProfit := 0;
  var hasIdx := false;
  var idx := 0;
  while i < n - 1
    invariant 0 <= i <= n - 1
    invariant 0 <= i <= |prices| - 1
    invariant maxProfit >= 0
    invariant forall j :: 0 <= j < i ==> ProfitForDay(prices, j, c) <= maxProfit
    invariant hasIdx ==> 0 <= idx < i && ProfitForDay(prices, idx, c) == maxProfit && maxProfit > 0
    invariant maxProfit > 0 ==> hasIdx
    decreases n - 1 - i
  {
    assert |prices| == n;
    assert 0 <= i;
    assert i < |prices| - 1;
    var p := ProfitForDay(prices, i, c);

    // compute updated state
    var newMax := if p > maxProfit then p else maxProfit;
    var newHasIdx := if p > maxProfit then true else hasIdx;
    var newIdx := if p > maxProfit then i else idx;

    // hints for preservation of invariants
    assert maxProfit <= newMax;
    assert p <= newMax;

    maxProfit := newMax;
    hasIdx := newHasIdx;
    idx := newIdx;

    i := i + 1;
  }

  // finalize result
  result := maxProfit;

  // helpful assertions to discharge existential in CorrectResult when result > 0
  if result > 0 {
    assert hasIdx;
    assert 0 <= idx < n - 1;
    assert ProfitForDay(prices, idx, c) == result;
  }
}
// </vc-code>

