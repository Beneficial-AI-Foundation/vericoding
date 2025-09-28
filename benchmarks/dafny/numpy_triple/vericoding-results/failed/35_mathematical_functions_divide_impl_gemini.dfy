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
/* helper modified by LLM (iteration 5): added lemma for division by zero cases */
lemma lemma_DivideFloat_by_zero(x1: FloatValue, x2: FloatValue)
    requires IsZero(x2)
    ensures if IsZero(x1) then
                DivideFloat(x1, x2).NaN?
            else
                DivideFloat(x1, x2).Infinity? || DivideFloat(x1, x2).NegInfinity?
{
}

/* helper modified by LLM (iteration 5): added lemma for finite division */
lemma lemma_DivideFloat_finite(x1: FloatValue, x2: FloatValue)
    requires x1.Finite? && x2.Finite? && !IsZero(x2)
    ensures var d := DivideFloat(x1, x2);
            d.Finite? && d.value == x1.value / x2.value && d.value * x2.value == x1.value
{
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
  /* code modified by LLM (iteration 5): used while loop with helper lemmas to prove postconditions */
  var i := 0;
  result := [];
  while i < |x1|
    invariant |result| == i
    invariant |x1| == |x2|
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
    if IsZero(x2[i]) {
        lemma_DivideFloat_by_zero(x1[i], x2[i]);
    } else if x1[i].Finite? && x2[i].Finite? {
        lemma_DivideFloat_finite(x1[i], x2[i]);
    }
    var val := DivideFloat(x1[i], x2[i]);
    result := result + [val];
    i := i + 1;
  }
}
// </vc-code>
