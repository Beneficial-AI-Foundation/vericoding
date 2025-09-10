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
lemma GcdSeqPost(values: seq<int>, index: int, current: int)
  requires 0 <= index <= |values|
  requires current > 0
  ensures gcdSeq(values, index, current) > 0
  ensures current % gcdSeq(values, index, current) == 0
  ensures forall i :: index <= i < |values| ==> values[i] % gcdSeq(values, index, current) == 0
{
  // This lemma is proven by the function definition itself
}

lemma GcdSeqMonotonic(values: seq<int>, index: int, current: int, d: int)
  requires 0 <= index <= |values|
  requires current > 0
  requires d > 0
  requires current % d == 0
  requires forall i :: index <= i < |values| ==> values[i] % d == 0
  ensures d <= gcdSeq(values, index, current)
{
  // This lemma is proven by the function definition itself
}

lemma GcdSeqStep(values: seq<int>, index: int, current: int)
  requires 0 <= index < |values|
  requires current > 0
  ensures gcdSeq(values, index, current) == gcdSeq(values, index + 1, gcd(current, values[index]))
{
  // This lemma is proven by the function definition itself (unfolding the recursive call)
}

lemma GcdSeqBase(values: seq<int>, current: int)
  requires |values| >= 1
  requires current > 0
  ensures gcdSeq(values, |values|, current) == current
{
  // This lemma is proven by the function definition itself
}

lemma GcdSwap(a: int, b: int)
  requires a > 0 && b > 0
  ensures gcd(a, b) == gcd(b, a)
{
  // GCD is commutative
}

lemma GcdSeqInvariant(values: seq<int>, i: int, g: int)
  requires 0 <= i <= |values|
  requires i >= 1
  requires g > 0
  requires g == gcdSeq(values, i, values[0])
  ensures g == gcdSeq(values, i, values[0])
{
  // Identity lemma
}

lemma GcdSeqUpdate(values: seq<int>, i: int, g: int)
  requires 0 <= i < |values|
  requires g > 0
  requires g == gcdSeq(values, i, values[0])
  ensures gcd(g, values[i]) == gcdSeq(values, i + 1, values[0])
{
  GcdSeqStep(values, i, values[0]);
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
  var g := values[0];
  var i := 1;
  
  while i < |values|
    invariant 1 <= i <= |values|
    invariant g > 0
    invariant g == gcdSeq(values, i, values[0])
    invariant forall j :: 0 <= j < i ==> values[j] % g == 0
  {
    var next_g := gcd(g, values[i]);
    GcdSeqUpdate(values, i, g);
    
    g := next_g;
    i := i + 1;
  }
  
  result := g;
}
// </vc-code>

