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
/* helper modified by LLM (iteration 5): lemma establishing target is a valid NextRepresentableValue when finite and different */
lemma NextRep_Finite_Target(x: Float, target: Float)
  requires IsFiniteFloat(x) && IsFiniteFloat(target) && x != target
  ensures IsNextRepresentableValue(x, target, target)
{
  if x.value < target.value {
    assert x.value < target.value && target.value <= target.value;
  } else {
    assert target.value <= target.value && target.value < x.value;
  }
}

/* helper modified by LLM (iteration 5): pure function mapping a pair of Floats to the NextAfter element */
function NextAfterElem(a: Float, b: Float): Float
{
  if IsNaN(a) || IsNaN(b) then NaN
  else if a == b then a
  else if IsPosInf(a) && IsFiniteFloat(b) then PosInf
  else if IsNegInf(a) && IsFiniteFloat(b) then NegInf
  else if IsFiniteFloat(a) && IsFiniteFloat(b) then b
  else if IsFiniteFloat(a) && IsPosInf(b) then PosInf
  else if IsFiniteFloat(a) && IsNegInf(b) then NegInf
  else b
}

/* helper modified by LLM (iteration 5): constructors for Float values */
function MakeFinite(v: real): Float { Finite(v) }

/* helper modified by LLM (iteration 5): NaN constructor */
function MakeNaN(): Float { NaN }

/* helper modified by LLM (iteration 5): positive infinity constructor */
function MakePosInf(): Float { PosInf }

/* helper modified by LLM (iteration 5): negative infinity constructor */
function MakeNegInf(): Float { NegInf }
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
  /* code modified by LLM (iteration 5): build result by mapping element-wise NextAfterElem */
  var n := |x1|;
  result := seq j | 0 <= j < n :: NextAfterElem(x1[j], x2[j]);
}

// </vc-code>
