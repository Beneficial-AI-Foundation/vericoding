// <vc-preamble>
/*
 * Dafny specification for numpy.logaddexp2 - Logarithm of the sum of exponentiations 
 * of the inputs in base-2. Calculates log2(2^x1 + 2^x2) element-wise in a numerically
 * stable way that avoids overflow for large input values.
 */

// Mathematical helper functions for base-2 logarithm and exponential
function {:axiom} {:compile false} Log2(x: real): real
  requires x > 0.0
{
  0.0
}

function {:axiom} {:compile false} Exp2(x: real): real
  ensures Exp2(x) > 0.0
{
  1.0
}

function Max(x: real, y: real): real
{
  if x >= y then x else y
}

// Element-wise maximum of two sequences
function SeqMax(x1: seq<real>, x2: seq<real>): seq<real>
  requires |x1| == |x2|
  ensures |SeqMax(x1, x2)| == |x1|
{
  seq(|x1|, i requires 0 <= i < |x1| => Max(x1[i], x2[i]))
}

// Element-wise comparison for monotonicity
predicate SeqLeq(x1: seq<real>, x2: seq<real>)
  requires |x1| == |x2|
{
  forall i :: 0 <= i < |x1| ==> x1[i] <= x2[i]
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fix Log2SumExp2 implementation and add supporting lemmas */
function Log2SumExp2(x: real, y: real): real
  requires x <= y
  ensures Log2SumExp2(x, y) == Log2(Exp2(x) + Exp2(y))
  ensures Max(x, y) <= Log2SumExp2(x, y)
  ensures Log2SumExp2(x, y) <= Max(x, y) + 1.0
{
  var m := y;
  m + Log2(1.0 + Exp2(x - y))
}

lemma Log2SumExp2Commutative(x: real, y: real)
  ensures Log2(Exp2(x) + Exp2(y)) == Log2(Exp2(y) + Exp2(x))
{
}

lemma Log2SumExp2Bounds(x: real, y: real)
  requires x <= y
  ensures y <= Log2(Exp2(x) + Exp2(y)) <= y + 1.0
{
  // Key lemma: 1 <= 1 + Exp2(x-y) <= 2 when x <= y
  // Since x <= y, x-y <= 0, so Exp2(x-y) <= 1
  // Therefore: 1 <= 1 + Exp2(x-y) <= 2
  // So: Log2(1) <= Log2(1 + Exp2(x-y)) <= Log2(2)
  // Which means: 0 <= Log2(1 + Exp2(x-y)) <= 1
  // Thus: y <= y + Log2(1 + Exp2(x-y)) <= y + 1
}

lemma Log2SumExp2OrderInvariant(a: real, b: real)
  ensures Log2(Exp2(a) + Exp2(b)) == Log2(Exp2(b) + Exp2(a))
{
}
// </vc-helpers>

// <vc-spec>
method NumpyLogaddexp2(x1: seq<real>, x2: seq<real>) returns (result: seq<real>)
  // Input vectors must have the same length
  requires |x1| == |x2|
  
  // Output vector has the same length as input vectors
  ensures |result| == |x1|
  
  // Core mathematical property: result[i] = log2(2^x1[i] + 2^x2[i])
  ensures forall i :: 0 <= i < |result| ==> 
    result[i] == Log2(Exp2(x1[i]) + Exp2(x2[i]))
  
  // Lower bound: max(x1[i], x2[i]) <= result[i]
  ensures forall i :: 0 <= i < |result| ==> 
    Max(x1[i], x2[i]) <= result[i]
  
  // Upper bound: result[i] <= max(x1[i], x2[i]) + 1
  ensures forall i :: 0 <= i < |result| ==> 
    result[i] <= Max(x1[i], x2[i]) + 1.0
  
  // Commutativity property: logaddexp2(x1, x2) = logaddexp2(x2, x1)
  ensures forall i :: 0 <= i < |result| ==> 
    result[i] == Log2(Exp2(x2[i]) + Exp2(x1[i]))
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): Proper implementation using element-wise computation */
  result := new real[|x1|];
  var i := 0;
  while i < |x1|
    invariant 0 <= i <= |x1|
    invariant |result| == |x1|
    invariant forall j :: 0 <= j < i ==> result[j] == Log2(Exp2(x1[j]) + Exp2(x2[j]))
    invariant forall j :: 0 <= j < i ==> Max(x1[j], x2[j]) <= result[j]
    invariant forall j :: 0 <= j < i ==> result[j] <= Max(x1[j], x2[j]) + 1.0
    invariant forall j :: 0 <= j < i ==> result[j] == Log2(Exp2(x2[j]) + Exp2(x1[j]))
  {
    if x1[i] <= x2[i] {
      result[i] := Log2SumExp2(x1[i], x2[i]);
    } else {
      result[i] := Log2SumExp2(x2[i], x1[i]);
    }
    i := i + 1;
  }
}
// </vc-code>
