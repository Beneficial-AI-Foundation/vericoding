// <vc-preamble>
// Datatype to represent floating point values including IEEE 754 special cases
datatype FloatValue = Finite(value: real) | Infinity | NegInfinity | NaN

// Helper predicate to check if a FloatValue is zero
predicate IsZero(f: FloatValue)
{
    f.Finite? && f.value == 0.0
}

// Helper predicate to check if a FloatValue is positive
predicate IsPositive(f: FloatValue)
{
    f.Finite? && f.value > 0.0
}

// Helper predicate to check if a FloatValue is negative
predicate IsNegative(f: FloatValue)
{
    f.Finite? && f.value < 0.0
}

// Division operation for FloatValues following IEEE 754 semantics
function DivideFloat(x1: FloatValue, x2: FloatValue): FloatValue
{
    if x1.NaN? || x2.NaN? then NaN
    else if x2.Infinity? || x2.NegInfinity? then
        if x1.Infinity? || x1.NegInfinity? then NaN
        else Finite(0.0)
    else if IsZero(x2) then
        if IsZero(x1) then NaN
        else if IsPositive(x1) then Infinity
        else NegInfinity
    else if x1.Infinity? then
        if IsPositive(x2) then Infinity else NegInfinity
    else if x1.NegInfinity? then
        if IsPositive(x2) then NegInfinity else Infinity
    else if x1.Finite? && x2.Finite? then
        Finite(x1.value / x2.value)
    else
        NaN
}

// Element-wise division method for vectors
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed syntax error by removing invalid forall statement */
lemma DivideFloatInfinityProperty(x1: FloatValue, x2: FloatValue)
  requires IsZero(x2) && !IsZero(x1)
  ensures DivideFloat(x1, x2).Infinity? || DivideFloat(x1, x2).NegInfinity?
{
  // The lemma follows from the definition of DivideFloat
}

lemma DivideFloatNaNProperty(x1: FloatValue, x2: FloatValue)
  requires IsZero(x2) && IsZero(x1)
  ensures DivideFloat(x1, x2).NaN?
{
  // The lemma follows from the definition of DivideFloat
}

lemma DivideFloatFiniteProperty(x1: FloatValue, x2: FloatValue)
  requires !IsZero(x2) && x1.Finite? && x2.Finite?
  ensures DivideFloat(x1, x2).Finite? && DivideFloat(x1, x2).value == x1.value / x2.value
{
  // The lemma follows from the definition of DivideFloat
}

lemma DivideFloatAllCasesProperty(x1: FloatValue, x2: FloatValue)
  ensures IsZero(x2) && !IsZero(x1) ==> (DivideFloat(x1, x2).Infinity? || DivideFloat(x1, x2).NegInfinity?)
  ensures IsZero(x2) && IsZero(x1) ==> DivideFloat(x1, x2).NaN?
  ensures !IsZero(x2) && x1.Finite? && x2.Finite? ==> (DivideFloat(x1, x2).Finite? && DivideFloat(x1, x2).value == x1.value / x2.value)
{
  if IsZero(x2) && !IsZero(x1) {
    DivideFloatInfinityProperty(x1, x2);
  } else if IsZero(x2) && IsZero(x1) {
    DivideFloatNaNProperty(x1, x2);
  } else if !IsZero(x2) && x1.Finite? && x2.Finite? {
    DivideFloatFiniteProperty(x1, x2);
  }
}
// </vc-helpers>

// <vc-spec>
method numpy_divide(x1: seq<FloatValue>, x2: seq<FloatValue>) returns (result: seq<FloatValue>)
    requires |x1| == |x2|
    ensures |result| == |x1|
    ensures forall i :: 0 <= i < |result| ==> result[i] == DivideFloat(x1[i], x2[i])
    ensures forall i :: 0 <= i < |result| && !IsZero(x2[i]) && x1[i].Finite? && x2[i].Finite? ==>
        result[i].Finite? && result[i].value == x1[i].value / x2[i].value
    ensures forall i :: 0 <= i < |result| && !IsZero(x2[i]) && x1[i].Finite? && x2[i].Finite? && result[i].Finite? ==>
        result[i].value * x2[i].value == x1[i].value
    ensures forall i :: 0 <= i < |result| && IsZero(x2[i]) && !IsZero(x1[i]) ==>
        result[i].Infinity? || result[i].NegInfinity?
    ensures forall i :: 0 <= i < |result| && IsZero(x2[i]) && IsZero(x1[i]) ==>
        result[i].NaN?
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): Removed invalid forall statement that caused compilation error */
  
  result := [];
  var i := 0;
  while i < |x1|
    invariant 0 <= i <= |x1|
    invariant |result| == i
    invariant forall j :: 0 <= j < i ==> result[j] == DivideFloat(x1[j], x2[j])
    invariant forall j :: 0 <= j < i && !IsZero(x2[j]) && x1[j].Finite? && x2[j].Finite? ==>
        result[j].Finite? && result[j].value == x1[j].value / x2[j].value
    invariant forall j :: 0 <= j < i && !IsZero(x2[j]) && x1[j].Finite? && x2[j].Finite? && result[j].Finite? ==>
        result[j].value * x2[j].value == x1[j].value
    invariant forall j :: 0 <= j < i && IsZero(x2[j]) && !IsZero(x1[j]) ==>
        result[j].Infinity? || result[j].NegInfinity?
    invariant forall j :: 0 <= j < i && IsZero(x2[j]) && IsZero(x1[j]) ==>
        result[j].NaN?
  {
    var div_result := DivideFloat(x1[i], x2[i]);
    if IsZero(x2[i]) && !IsZero(x1[i]) {
      DivideFloatInfinityProperty(x1[i], x2[i]);
    } else if IsZero(x2[i]) && IsZero(x1[i]) {
      DivideFloatNaNProperty(x1[i], x2[i]);
    } else if !IsZero(x2[i]) && x1[i].Finite? && x2[i].Finite? {
      DivideFloatFiniteProperty(x1[i], x2[i]);
    }
    result := result + [div_result];
    i := i + 1;
  }
}
// </vc-code>
