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

lemma GcdCommutative(a: int, b: int)
  requires a > 0 && b > 0
  ensures gcd(a, b) == gcd(b, a)
{
  if a == b {
  } else if a > b {
    GcdCommutative(a - b, b);
  } else {
    GcdCommutative(a, b - a);
  }
}

lemma GcdDivisible(a: int, b: int)
  requires a > 0 && b > 0
  ensures a % gcd(a, b) == 0 && b % gcd(a, b) == 0
{
  if a == b {
  } else if a > b {
    GcdDivisible(a - b, b);
    var g := gcd(a - b, b);
    calc {
      gcd(a, b);
      gcd(a - b, b);
      g;
    }
    assert a - b == (a - b) / g * g;
    assert a == (a - b) + b;
    assert a == ((a - b) / g + b / g) * g;
    assert a % g == 0;
  } else {
    GcdDivisible(a, b - a);
    var g := gcd(a, b - a);
    calc {
      gcd(a, b);
      gcd(a, b - a);
      g;
    }
    assert b - a == (b - a) / g * g;
    assert b == a + (b - a);
    assert b == (a / g + (b - a) / g) * g;
    assert b % g == 0;
  }
}

lemma GcdGreatest(a: int, b: int, d: int)
  requires a > 0 && b > 0
  requires d > 0
  requires a % d == 0 && b % d == 0
  ensures d <= gcd(a, b)
{
  if a == b {
    calc {
      a % d;
      0;
    }
    assert a == d * (a / d);
    if d > a {
      assert a / d == 0;
      assert a == 0;
      assert false;
    }
  } else if a > b {
    assert (a - b) % d == 0;
    GcdGreatest(a - b, b, d);
  } else {
    assert (b - a) % d == 0;
    GcdGreatest(a, b - a, d);
  }
}

lemma GcdSeqProperty(values: seq<int>, index: int, current: int, new_g: int)
  requires 0 <= index < |values|
  requires current > 0
  requires forall i :: 0 <= i < |values| ==> values[i] > 0
  requires new_g == gcd(current, values[index])
  ensures gcdSeq(values, index + 1, current) == gcdSeq(values, index + 1, new_g)
{
  calc {
    gcd
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

lemma GcdCommutative(a: int, b: int)
  requires a > 0 && b > 0
  ensures gcd(a, b) == gcd(b, a)
{
  if a == b {
  } else if a > b {
    GcdCommutative(a - b, b);
  } else {
    GcdCommutative(a, b - a);
  }
}

lemma GcdDivisible(a: int, b: int)
  requires a > 0 && b > 0
  ensures a % gcd(a, b) == 0 && b % gcd(a, b) == 0
{
  if a == b {
  } else if a > b {
    GcdDivisible(a - b, b);
    var g := gcd(a - b, b);
    calc {
      gcd(a, b);
      gcd(a - b, b);
      g;
    }
    assert a - b == (a - b) / g * g;
    assert a == (a - b) + b;
    assert a == ((a - b) / g + b / g) * g;
    assert a % g == 0;
  } else {
    GcdDivisible(a, b - a);
    var g := gcd(a, b - a);
    calc {
      gcd(a, b);
      gcd(a, b - a);
      g;
    }
    assert b - a == (b - a) / g * g;
    assert b == a + (b - a);
    assert b == (a / g + (b - a) / g) * g;
    assert b % g == 0;
  }
}

lemma GcdGreatest(a: int, b: int, d: int)
  requires a > 0 && b > 0
  requires d > 0
  requires a % d == 0 && b % d == 0
  ensures d <= gcd(a, b)
{
  if a == b {
    calc {
      a % d;
      0;
    }
    assert a == d * (a / d);
    if d > a {
      assert a / d == 0;
      assert a == 0;
      assert false;
    }
  } else if a > b {
    assert (a - b) % d == 0;
    GcdGreatest(a - b, b, d);
  } else {
    assert (b - a) % d == 0;
    GcdGreatest(a, b - a, d);
  }
}

lemma GcdSeqProperty(values: seq<int>, index: int, current: int, new_g: int)
  requires 0 <= index < |values|
  requires current > 0
  requires forall i :: 0 <= i < |values| ==> values[i] > 0
  requires new_g == gcd(current, values[index])
  ensures gcdSeq(values, index + 1, current) == gcdSeq(values, index + 1, new_g)
{
  calc {
    gcd
// </vc-code>

