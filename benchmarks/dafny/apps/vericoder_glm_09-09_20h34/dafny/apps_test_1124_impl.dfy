predicate ValidInput(values: seq<int>)
{
  |values| >= 1 && forall i :: 0 <= i < |values| ==> values[i] > 0
}

function gcd(a: int, b: int): int
  requires a > 0 && b > 0
  decreases if a >= b then a else b
  ensures gcd(a, b) > 0
  ensures a % gcd(a, b) == 0
  ensures b % gcd(a, b) == 0
  ensures forall d :: d > 0 && a % d == 0 && b % d == 0 ==> d <= gcd(a, b)
{
  if a == b then a
  else if a > b then gcd(a - b, b)
  else gcd(a, b - a)
}

function gcdSeq(values: seq<int>, index: int, current: int): int
  requires 0 <= index <= |values|
  requires current > 0
  requires forall i :: 0 <= i < |values| ==> values[i] > 0
  decreases |values| - index
  ensures gcdSeq(values, index, current) > 0
  ensures current % gcdSeq(values, index, current) == 0
  ensures forall i :: index <= i < |values| ==> values[i] % gcdSeq(values, index, current) == 0
  ensures forall d {:trigger current % d} :: d > 0 && current % d == 0 && (forall i :: index <= i < |values| ==> values[i] % d == 0) ==> d <= gcdSeq(values, index, current)
{
  if index == |values| then current
  else gcdSeq(values, index + 1, gcd(current, values[index]))
}

function gcdOfAll(values: seq<int>): int
  requires |values| >= 1
  requires forall i :: 0 <= i < |values| ==> values[i] > 0
  ensures gcdOfAll(values) > 0
  ensures forall i :: 0 <= i < |values| ==> values[i] % gcdOfAll(values) == 0
  ensures forall d {:trigger values[0] % d} :: d > 0 && (forall i :: 0 <= i < |values| ==> values[i] % d == 0) ==> d <= gcdOfAll(values)
{
  gcdSeq(values, 1, values[0])
}

// <vc-helpers>
lemma LemmaGcdUpdate(values: seq<int>, i: int, old_current: int)
  requires 0 <= i < |values|
  requires old_current > 0
  requires forall j :: 0 <= j < i ==> values[j] % old_current == 0
  requires forall d :: d > 0 && (forall j :: 0 <= j < i ==> values[j] % d == 0) ==> d <= old_current
  ensures forall d :: d > 0 && (forall j :: 0 <= j < i + 1 ==> values[j] % d == 0) ==> d <= gcd(old_current, values[i])
{
  forall d | d > 0 && (forall j :: 0 <= j < i+1 ==> values[j] % d == 0)
  ensures d <= gcd(old_current, values[i])
  {
    forall j | 0 <= j < i ensures values[j] % d == 0 {}
    assert d <= old_current;
    assert d > 0;
    assert values[i] % d == 0;
    assert d <= gcd(old_current, values[i]);
  }
}

lemma BaseCase(value: int)
  requires value > 0
  ensures forall d :: d > 0 && value % d == 0 ==> d <= value
{
  forall d | d > 0 && value % d == 0 ensures d <= value
  {
    assert value as nat == d as nat * (value / d);
    assert (value / d) > 0;
    calc {
      d * 1 <= d * (value / d);
      == { assert d as nat * 1 == d; }
      d <= value;
    }
  }
}
// </vc-helpers>

// <vc-spec>
method solve(values: seq<int>) returns (result: int)
  requires ValidInput(values)
  ensures result > 0
  ensures result == gcdOfAll(values)
  ensures forall i :: 0 <= i < |values| ==> values[i] % result == 0
  ensures forall d
// </vc-spec>
// <vc-code>
{
  if |values| == 1 {
    BaseCase(values[0]);
    return values[0];
  } else {
    var current := values[0];
    var i := 1;
    BaseCase(values[0]);
    while i < |values|
      invariant 1 <= i <= |values|
      invariant current > 0
      invariant forall j :: 0 <= j < i ==> values[j] % current == 0
      invariant forall d :: d > 0 && (forall j :: 0 <= j < i ==> values[j] % d == 0) ==> d <= current
    {
      ghost var old_current := current;
      current := gcd(old_current, values[i]);
      LemmaGcdUpdate(values, i, old_current);
      i := i + 1;
    }
    return current;
  }
}
// </vc-code>

