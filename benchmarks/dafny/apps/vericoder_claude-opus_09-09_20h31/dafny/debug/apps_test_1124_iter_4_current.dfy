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
lemma gcdSeqFromIndex(values: seq<int>, index: int, current: int)
  requires 0 <= index <= |values|
  requires current > 0
  requires forall i :: 0 <= i < |values| ==> values[i] > 0
  ensures index < |values| ==> gcdSeq(values, index, current) == gcdSeq(values, index + 1, gcd(current, values[index]))
  ensures index == |values| ==> gcdSeq(values, index, current) == current
{
  // This lemma follows directly from the definition of gcdSeq
}

lemma gcdOfAllIsGcdSeq(values: seq<int>)
  requires |values| >= 1
  requires forall i :: 0 <= i < |values| ==> values[i] > 0
  ensures gcdOfAll(values) == gcdSeq(values, 1, values[0])
{
  // This follows from the definition of gcdOfAll
}

lemma gcdSeqPrefix(values: seq<int>, k: int)
  requires 1 <= k <= |values|
  requires forall i :: 0 <= i < |values| ==> values[i] > 0
  ensures gcdSeq(values, k, gcdSeq(values, 1, values[0])) == gcdSeq(values, 1, values[0])
  decreases |values| - k
{
  if k == |values| {
    // Base case: gcdSeq(values, |values|, current) == current
  } else {
    // Inductive case
    var current := gcdSeq(values, 1, values[0]);
    assert gcdSeq(values, k, current) == gcdSeq(values, k + 1, gcd(current, values[k]));
    
    // We need to show that gcd(current, values[k]) == current
    // This follows from the fact that values[k] % current == 0
    assert values[k] % current == 0;
    assert gcd(current, values[k]) == current;
    
    gcdSeqPrefix(values, k + 1);
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
  var i := 1;
  result := values[0];
  
  while i < |values|
    invariant 1 <= i <= |values|
    invariant result > 0
    invariant result == gcdSeq(values, i, values[0])
    invariant forall j :: 0 <= j < i ==> values[j] % result == 0
  {
    result := gcd(result, values[i]);
    i := i + 1;
  }
  
  assert i == |values|;
  assert result == gcdSeq(values, |values|, values[0]);
  assert gcdSeq(values, |values|, values[0]) == values[0];
  
  // Since result == values[0] when i == |values|, and we need result == gcdOfAll(values)
  // We need to recalculate properly
  
  i := 1;
  result := values[0];
  
  while i < |values|
    invariant 1 <= i <= |values|
    invariant result > 0
    invariant result == gcdSeq(values[0..i], 1, values[0])
    invariant forall j :: 0 <= j < i ==> values[j] % result == 0
  {
    var prev := result;
    result := gcd(result, values[i]);
    i := i + 1;
    assert values[0..i] == values[0..i-1] + [values[i-1]];
  }
  
  assert i == |values|;
  assert values[0..|values|] == values;
  gcdOfAllIsGcdSeq(values);
}
// </vc-code>

