// <vc-preamble>
// Datatype to represent IEEE 754-like floating-point values
datatype Float = Finite(value: real) | PosInf | NegInf | NaN

// Predicate to check if a Float value represents positive infinity
predicate IsPositiveInfinity(x: Float)
{
    x.PosInf?
}

// Predicate to check if a Float value represents negative infinity  
predicate IsNegativeInfinity(x: Float)
{
    x.NegInf?
}

// Predicate to check if a Float value represents NaN (Not a Number)
predicate IsNaN(x: Float)
{
    x.NaN?
}

// Predicate to check if a Float value represents any form of infinity
predicate IsInfinity(x: Float)
{
    IsPositiveInfinity(x) || IsNegativeInfinity(x)
}

// Predicate to check if a Float value is finite (not infinity and not NaN)
predicate IsFinite(x: Float)
{
    !IsInfinity(x) && !IsNaN(x)
}

// Method that tests element-wise for finiteness in an array
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): executable bool version of finiteness compatible with current function syntax */
function IsFiniteBool(x: Float): bool
{
  match x
  case Finite(v) => true
  case PosInf => false
  case NegInf => false
  case NaN => false
}

/* helper modified by LLM (iteration 3): lemma linking executable and logical finiteness */
lemma IsFiniteBoolSpec(x: Float)
  ensures IsFiniteBool(x) <==> IsFinite(x)
{
  match x
  case Finite(v) =>
  case PosInf =>
  case NegInf =>
  case NaN =>
}
// </vc-helpers>

// <vc-spec>
method IsFiniteArray(x: seq<Float>) returns (result: seq<bool>)
    ensures |result| == |x|
    ensures forall i :: 0 <= i < |x| ==> 
        // Core equivalence: result is true iff input element is finite
        (result[i] <==> IsFinite(x[i]))
    ensures forall i :: 0 <= i < |x| ==> 
        // Inverse property: result is false iff input is NaN or infinity
        (result[i] == false <==> (IsNaN(x[i]) || IsInfinity(x[i])))
    ensures forall i :: 0 <= i < |x| ==> 
        // Decomposition: finite means not NaN and not infinity
        (result[i] == true <==> (!IsNaN(x[i]) && !IsInfinity(x[i])))
    ensures forall i :: 0 <= i < |x| ==> 
        // Specific case: zero is always finite
        (x[i] == Finite(0.0) ==> result[i] == true)
    ensures forall i :: 0 <= i < |x| ==> 
        // IEEE 754 compliance: finite values exclude special values
        (result[i] == true ==> (!IsNaN(x[i]) && !IsInfinity(x[i])))
    ensures forall i :: 0 <= i < |x| ==> 
        // Consistency: if not finite, then must be NaN or infinity
        (result[i] == false ==> (IsNaN(x[i]) || IsInfinity(x[i])))
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 3): iterative construction using helper and loop invariants */
  var i := 0;
  var res: seq<bool> := [];
  while i < |x|
    invariant 0 <= i <= |x|
    invariant |res| == i
    invariant forall j :: 0 <= j < i ==> (res[j] <==> IsFinite(x[j]))
    decreases |x| - i
  {
    var b := IsFiniteBool(x[i]);
    IsFiniteBoolSpec(x[i]);
    res := res + [b];
    i := i + 1;
  }
  result := res;
}
// </vc-code>
