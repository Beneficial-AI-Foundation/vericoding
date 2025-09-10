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
lemma GcdSeqProperty(values: seq<int>, index: int, current: int)
  requires 0 <= index <= |values|
  requires current > 0
  requires forall i :: 0 <= i < |values| ==> values[i] > 0
  ensures gcdSeq(values, index, current) > 0
  ensures current % gcdSeq(values, index, current) == 0
  ensures forall i :: index <= i < |values| ==> values[i] % gcdSeq(values, index, current) == 0
{
  // Proof by induction on the decreasing measure |values| - index
}

lemma GcdSeqStep(values: seq<int>, index: int, current: int)
  requires 0 <= index < |values|
  requires current > 0
  requires forall i :: 0 <= i < |values| ==> values[i] > 0
  ensures gcdSeq(values, index, current) == gcdSeq(values, index + 1, gcd(current, values[index]))
{
  // This follows directly from the definition of gcdSeq
}

lemma LoopInvariantMaintained(values: seq<int>, index: int, current: int)
  requires 1 <= index < |values|
  requires current > 0
  requires forall i :: 0 <= i < |values| ==> values[i] > 0
  requires forall i :: 0 <= i < index ==> values[i] % current == 0
  requires current == gcdSeq(values, index, current)
  ensures var newCurrent := gcd(current, values[index]);
          newCurrent > 0 &&
          (forall i :: 0 <= i <= index ==> values[i] % newCurrent == 0) &&
          newCurrent == gcdSeq(values, index + 1, newCurrent)
{
  var newCurrent := gcd(current, values[index]);
  GcdSeqStep(values, index, current);
  assert newCurrent == gcdSeq(values, index + 1, newCurrent);
}

lemma GcdSeqBaseCase(values: seq<int>)
  requires |values| >= 1
  requires forall i :: 0 <= i < |values| ==> values[i] > 0
  ensures values[0] == gcdSeq(values, 1, values[0])
{
  // Base case for the loop invariant
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
    return values[0];
  }
  
  var current := values[0];
  var index := 1;
  
  GcdSeqBaseCase(values);
  
  while index < |values|
    invariant 1 <= index <= |values|
    invariant current > 0
    invariant forall i :: 0 <= i < index ==> values[i] % current == 0
    invariant current == gcdSeq(values, index, current)
  {
    LoopInvariantMaintained(values, index, current);
    current := gcd(current, values[index]);
    index := index + 1;
  }
  
  assert index == |values|;
  assert current == gcdSeq(values, |values|, current);
  assert current == gcdOfAll(values);
  
  return current;
}
// </vc-code>

