predicate ValidInput(n: int, m: int, k: int, emotes: seq<int>)
{
    n >= 2 && k >= 1 && m >= 1 && |emotes| == n &&
    forall i :: 0 <= i < |emotes| ==> emotes[i] >= 1
}

function MaxHappiness(n: int, m: int, k: int, emotes: seq<int>): int
    requires ValidInput(n, m, k, emotes)
{
    var k_plus_1 := k + 1;
    var total := m / k_plus_1;
    var remainder := m % k_plus_1;
    // Assumes optimal strategy using highest and second highest values
    var max_val := MaxValue(emotes);
    var second_max_val := SecondMaxValue(emotes);
    remainder * max_val + max_val * (total * k) + second_max_val * total
}

function MaxValue(s: seq<int>): int
    requires |s| >= 1
    requires forall i :: 0 <= i < |s| ==> s[i] >= 1
    ensures MaxValue(s) >= 1
    ensures exists i :: 0 <= i < |s| && s[i] == MaxValue(s)
{
    if |s| == 1 then s[0]
    else if s[0] >= MaxValue(s[1..]) then s[0]
    else MaxValue(s[1..])
}

function SecondMaxValue(s: seq<int>): int
    requires |s| >= 2
    requires forall i :: 0 <= i < |s| ==> s[i] >= 1
{
    var max_val := MaxValue(s);
    var filtered := FilterOut(s, max_val, 1);
    if |filtered| > 0 then MaxValue(filtered) else 1
}

function FilterOut(s: seq<int>, val: int, count: int): seq<int>
    requires count >= 0
    requires forall i :: 0 <= i < |s| ==> s[i] >= 1
    ensures forall i :: 0 <= i < |FilterOut(s, val, count)| ==> FilterOut(s, val, count)[i] >= 1
{
    if |s| == 0 || count == 0 then s
    else if s[0] == val then FilterOut(s[1..], val, count - 1)
    else [s[0]] + FilterOut(s[1..], val, count)
}

// <vc-helpers>
lemma SecondMaxAtLeastOne(s: seq<int>)
  requires |s| >= 2
  requires forall i :: 0 <= i < |s| ==> s[i] >= 1
  ensures SecondMaxValue(s) >= 1
{
  var max_val := MaxValue(s);
  var filtered := FilterOut(s, max_val, 1);
  assert SecondMaxValue(s) == (if |filtered| > 0 then MaxValue(filtered) else 1);
  if |filtered| > 0 {
    assert forall i :: 0 <= i < |filtered| ==> filtered[i] >= 1;
    assert MaxValue(filtered) >= 1;
  } else {
    assert SecondMaxValue(s) == 1;
  }
}

lemma MaxHappinessNonNeg(n: int, m: int, k: int, emotes: seq<int>)
  requires ValidInput(n, m, k, emotes)
  ensures MaxHappiness(n, m, k, emotes) >= 0
{
  // Basic non-negativity facts about division and modulo
  var k1 := k + 1;
  assert k1 > 0;
  var total := m / k1;
  var rem := m % k1;
  assert 0 <= rem < k1;
  assert m == total * k1 + rem;
  if total < 0 {
    assert total <= -1;
    assert total * k1 <= -k1;
    assert m <= -k1 + rem;
    assert -k1 + rem <= -1;
    assert false;
  }
  // Values are at least 1
  assert MaxValue(emotes) >= 1;
  assert |emotes| == n;
  assert |emotes| >= 2;
  SecondMaxAtLeastOne(emotes);
  assert SecondMaxValue(emotes) >= 1;

  // Tie to definition of MaxHappiness
  assert MaxHappiness(n, m, k, emotes) ==
    rem * MaxValue(emotes) +
    MaxValue(emotes) * (total * k) +
    SecondMaxValue(emotes) * total;

  // Each term is non-negative
  assert rem * MaxValue(emotes) >= 0;
  assert total * k >= 0;
  assert MaxValue(emotes) * (total * k) >= 0;
  assert SecondMaxValue(emotes) * total >= 0;

  // Sum is non-negative
  assert rem * MaxValue(emotes) +
         MaxValue(emotes) * (total * k) +
         SecondMaxValue(emotes) * total >= 0;
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, m: int, k: int, emotes: seq<int>) returns (result: int)
    requires ValidInput(n, m, k, emotes)
    ensures result >= 0
// </vc-spec>
// <vc-code>
{
  result := MaxHappiness(n, m, k, emotes);
  MaxHappinessNonNeg(n, m, k, emotes);
  assert result >= 0;
}
// </vc-code>

