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
lemma DividesTransitive(a: int, b: int, c: int)
  requires a > 0 && b != 0
  requires b % a == 0
  requires c % b == 0
  ensures c % a == 0
{
  if b % a == 0 && c % b == 0 {
    var k1 := c / b;
    var k2 := b / a;
    assert c == k1 * b;
    assert b == k2 * a;
    assert c == k1 * (k2 * a);
    assert c == (k1 * k2) * a;
    assert c % a == 0;
  }
}

lemma GcdProperty(a: int, b: int, d: int)
  requires a > 0 && b > 0 && d > 0
  requires a % d == 0 && b % d == 0
  ensures gcd(a, b) % d == 0
  decreases a + b
{
  if a == b {
  } else if a > b {
    assert (a - b) % d == 0;
    GcdProperty(a - b, b, d);
  } else {
    assert (b - a) % d == 0;
    GcdProperty(a, b - a, d);
  }
}

lemma GcdGreat
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
lemma DividesTransitive(a: int, b: int, c: int)
  requires a > 0 && b != 0
  requires b % a == 0
  requires c % b == 0
  ensures c % a == 0
{
  if b % a == 0 && c % b == 0 {
    var k1 := c / b;
    var k2 := b / a;
    assert c == k1 * b;
    assert b == k2 * a;
    assert c == k1 * (k2 * a);
    assert c == (k1 * k2) * a;
    assert c % a == 0;
  }
}

lemma GcdProperty(a: int, b: int, d: int)
  requires a > 0 && b > 0 && d > 0
  requires a % d == 0 && b % d == 0
  ensures gcd(a, b) % d == 0
  decreases a + b
{
  if a == b {
  } else if a > b {
    assert (a - b) % d == 0;
    GcdProperty(a - b, b, d);
  } else {
    assert (b - a) % d == 0;
    GcdProperty(a, b - a, d);
  }
}

lemma GcdGreat
// </vc-code>

