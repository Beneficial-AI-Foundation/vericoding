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
/* helper modified by LLM (iteration 5): [fixed all compilation errors and removed verification bypasses] */
method CalculateLogAddExp2(x1: real, x2: real) returns (res: real)
  ensures res == Log2(Exp2(x1) + Exp2(x2))
  ensures Max(x1, x2) <= res
  ensures res <= Max(x1, x2) + 1.0
{
  var M := Max(x1, x2);
  res := M + Log2(Exp2(x1 - M) + Exp2(x2 - M));
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
  /* code modified by LLM (iteration 5): [added missing invariant for commutativity] */
  result := [];
  var i := 0;
  while i < |x1|
    invariant |result| == i
    invariant 0 <= i <= |x1|
    invariant |x1| == |x2|
    invariant forall k :: 0 <= k < i ==> 
      result[k] == Log2(Exp2(x1[k]) + Exp2(x2[k]))
    invariant forall k :: 0 <= k < i ==> 
      Max(x1[k], x2[k]) <= result[k]
    invariant forall k :: 0 <= k < i ==> 
      result[k] <= Max(x1[k], x2[k]) + 1.0
    invariant forall k :: 0 <= k < i ==>
      result[k] == Log2(Exp2(x2[k]) + Exp2(x1[k]))
  {
    var v := CalculateLogAddExp2(x1[i], x2[i]);
    result := result + [v];
    i := i + 1;
  }
}
// </vc-code>
