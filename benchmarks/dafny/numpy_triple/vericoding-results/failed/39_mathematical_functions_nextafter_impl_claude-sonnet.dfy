// <vc-preamble>
// Datatype to represent floating-point values
datatype Float = 
  | Finite(value: real)
  | PosInf
  | NegInf  
  | NaN

// Predicate to check if a float represents a finite floating-point value
predicate IsFiniteFloat(x: Float)
{
  x.Finite?
}

// Predicate to check if a float represents positive infinity
predicate IsPosInf(x: Float)
{
  x.PosInf?
}

// Predicate to check if a float represents negative infinity  
predicate IsNegInf(x: Float)
{
  x.NegInf?
}

// Predicate to check if a float represents NaN
predicate IsNaN(x: Float)
{
  x.NaN?
}

// Predicate to check if y is the immediate next representable floating-point value after x towards target
predicate IsNextRepresentableValue(x: Float, target: Float, y: Float)
{
  if x == target then false
  else if IsFiniteFloat(x) && IsFiniteFloat(target) && IsFiniteFloat(y) then
    if x.value < target.value then x.value < y.value && y.value <= target.value
    else target.value <= y.value && y.value < x.value
  else false
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): function that satisfies IsNextRepresentableValue predicate with fixed logic */
function NextValue(x: Float, target: Float): Float
{
  if x == target then x
  else if IsNaN(x) || IsNaN(target) then NaN
  else if IsPosInf(x) && IsFiniteFloat(target) then PosInf
  else if IsNegInf(x) && IsFiniteFloat(target) then NegInf
  else if IsFiniteFloat(x) && IsFiniteFloat(target) then
    if x.value < target.value then
      var nextVal := x.value + 0.1;
      if nextVal <= target.value then Finite(nextVal) else Finite(target.value)
    else
      var nextVal := x.value - 0.1;
      if nextVal >= target.value then Finite(nextVal) else Finite(target.value)
  else if IsFiniteFloat(x) && IsPosInf(target) then Finite(x.value + 1.0)
  else if IsFiniteFloat(x) && IsNegInf(target) then Finite(x.value - 1.0)
  else x
}

/* helper modified by LLM (iteration 5): lemma that proves NextValue satisfies IsNextRepresentableValue for all finite cases */
lemma NextValueProof(x: Float, target: Float)
  requires x != target
  requires IsFiniteFloat(x) && IsFiniteFloat(target)
  ensures IsNextRepresentableValue(x, target, NextValue(x, target))
{
  var result := NextValue(x, target);
  if x.value < target.value {
    var nextVal := x.value + 0.1;
    if nextVal <= target.value {
      assert result == Finite(nextVal);
      assert x.value < result.value && result.value <= target.value;
    } else {
      assert result == Finite(target.value);
      assert x.value < result.value && result.value <= target.value;
    }
  } else {
    var nextVal := x.value - 0.1;
    if nextVal >= target.value {
      assert result == Finite(nextVal);
      assert target.value <= result.value && result.value < x.value;
    } else {
      assert result == Finite(target.value);
      assert target.value <= result.value && result.value < x.value;
    }
  }
}
// </vc-helpers>

// <vc-spec>
method NextAfter(x1: seq<Float>, x2: seq<Float>) returns (result: seq<Float>)
  // Precondition: input sequences must have the same length
  requires |x1| == |x2|
  
  // Postcondition: output has same length as inputs
  ensures |result| == |x1|
  
  // Postcondition: element-wise properties
  ensures forall i :: 0 <= i < |result| ==>
    // Identity case: when x1 equals x2, result equals x1
    (x1[i] == x2[i] ==> result[i] == x1[i]) &&
    
    // Direction consistency: result moves towards x2
    (IsFiniteFloat(x1[i]) && IsFiniteFloat(x2[i]) && x1[i].value < x2[i].value ==> 
     IsFiniteFloat(result[i]) && x1[i].value < result[i].value && result[i].value <= x2[i].value) &&
    (IsFiniteFloat(x1[i]) && IsFiniteFloat(x2[i]) && x1[i].value > x2[i].value ==> 
     IsFiniteFloat(result[i]) && x2[i].value <= result[i].value && result[i].value < x1[i].value) &&
    
    // Minimal step property: result is the immediate next representable value
    (x1[i] != x2[i] ==> IsNextRepresentableValue(x1[i], x2[i], result[i])) &&
    
    // Special cases for infinity
    (IsPosInf(x1[i]) && IsFiniteFloat(x2[i]) ==> IsPosInf(result[i])) &&
    (IsNegInf(x1[i]) && IsFiniteFloat(x2[i]) ==> IsNegInf(result[i])) &&
    
    // NaN propagation
    (IsNaN(x1[i]) || IsNaN(x2[i]) ==> IsNaN(result[i])) &&
    
    // Finiteness preservation: if both inputs are finite and different, 
    // result is finite unless at floating-point boundary
    (IsFiniteFloat(x1[i]) && IsFiniteFloat(x2[i]) && x1[i] != x2[i] ==> 
     IsFiniteFloat(result[i]) || IsPosInf(result[i]) || IsNegInf(result[i]))
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): add explicit proof case for IsNextRepresentableValue */
  result := [];
  var i := 0;
  while i < |x1|
    invariant 0 <= i <= |x1|
    invariant |result| == i
    invariant forall j :: 0 <= j < i ==>
      (x1[j] == x2[j] ==> result[j] == x1[j]) &&
      (IsFiniteFloat(x1[j]) && IsFiniteFloat(x2[j]) && x1[j].value < x2[j].value ==> 
       IsFiniteFloat(result[j]) && x1[j].value < result[j].value && result[j].value <= x2[j].value) &&
      (IsFiniteFloat(x1[j]) && IsFiniteFloat(x2[j]) && x1[j].value > x2[j].value ==> 
       IsFiniteFloat(result[j]) && x2[j].value <= result[j].value && result[j].value < x1[j].value) &&
      (x1[j] != x2[j] ==> IsNextRepresentableValue(x1[j], x2[j], result[j])) &&
      (IsPosInf(x1[j]) && IsFiniteFloat(x2[j]) ==> IsPosInf(result[j])) &&
      (IsNegInf(x1[j]) && IsFiniteFloat(x2[j]) ==> IsNegInf(result[j])) &&
      (IsNaN(x1[j]) || IsNaN(x2[j]) ==> IsNaN(result[j])) &&
      (IsFiniteFloat(x1[j]) && IsFiniteFloat(x2[j]) && x1[j] != x2[j] ==> 
       IsFiniteFloat(result[j]) || IsPosInf(result[j]) || IsNegInf(result[j]))
  {
    if x1[i] != x2[i] && IsFiniteFloat(x1[i]) && IsFiniteFloat(x2[i]) {
      NextValueProof(x1[i], x2[i]);
    }
    result := result + [NextValue(x1[i], x2[i])];
    i := i + 1;
  }
}
// </vc-code>
