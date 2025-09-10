function sum(cards: seq<int>): int
{
    if |cards| == 0 then 0
    else cards[0] + sum(cards[1..])
}

function abs(x: int): int
{
    if x >= 0 then x else -x
}

predicate ValidInput(cards: seq<int>, x: int)
{
    x > 0 && |cards| >= 1 && forall i :: 0 <= i < |cards| ==> -x <= cards[i] <= x
}

// <vc-helpers>
lemma SumProperties(cards: seq<int>, x: int)
  requires ValidInput(cards, x)
  ensures sum(cards) >= -x * |cards| && sum(cards) <= x * |cards|
{
  if |cards| == 0 {
  } else {
    // Prove that the tail also satisfies ValidInput
    assert |cards[1..]| >= 0;
    assert forall i :: 0 <= i < |cards[1..]| ==> -x <= cards[1..][i] <= x;
    SumProperties(cards[1..], x);
  }
}

lemma DivisionLemma(a: int, d: int)
  requires d > 0
  ensures (a + d - 1) / d == if a % d == 0 then a / d else a / d + 1
{
}

lemma DivisionNonNegative(a: int, d: int)
  requires d > 0 && a >= 0
  ensures (a + d - 1) / d >= 0
{
}

lemma AbsSumNonNegative(cards: seq<int>, x: int)
  requires ValidInput(cards, x)
  ensures abs(sum(cards)) >= 0
{
  SumProperties(cards, x);
}
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
method solve(cards: seq<int>, x: int) returns (result: int)
    requires ValidInput(cards, x)
    ensures result >= 0
    ensures result == if sum(cards) == 0 then 0 else (abs(sum(cards)) + x - 1) / x
// </vc-spec>
// <vc-code>
{
  var total := sum(cards);
  if total == 0 {
    result := 0;
  } else {
    var absTotal := abs(total);
    DivisionNonNegative(absTotal, x);
    result := (absTotal + x - 1) / x;
  }
}
// </vc-code>

