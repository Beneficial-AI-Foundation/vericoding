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
predicate OptionallyFinite(f: FloatValue)
{
    f.Finite? || f.Infinity? || f.NegInfinity?
}

lemma DivisionProperties(x1: FloatValue, x2: FloatValue)
    ensures OptionallyFinite(x1) && OptionallyFinite(x2) && !IsZero(x2) ==> OptionallyFinite(DivideFloat(x1, x2))
    ensures IsZero(x2) && !IsZero(x1) ==> (DivideFloat(x1, x2)).Infinity? || (DivideFloat(x1, x2)).NegInfinity?
    ensures IsZero(x2) && IsZero(x1) ==> (DivideFloat(x1, x2)).NaN?
{
    /* helper modified by LLM (iteration 5): Complete case analysis with proper assertions */
    if x1.NaN? || x2.NaN? {
        // Case 1: One or both are NaN - result is NaN
        assert DivideFloat(x1, x2) == NaN;
    } else if x2.Infinity? || x2.NegInfinity? {
        // Case 2: x2 is infinity - result is 0 if x1 is finite, NaN if x1 is infinite
        if x1.Infinity? || x1.NegInfinity? {
            // result is NaN
            assert DivideFloat(x1, x2) == NaN;
        } else {
            // result is Finite(0.0)
            assert DivideFloat(x1, x2) == Finite(0.0);
            assert OptionallyFinite(DivideFloat(x1, x2));
        }
    } else if IsZero(x2) {
        // Case 3: x2 is zero
        if IsZero(x1) {
            // result is NaN
            assert DivideFloat(x1, x2) == NaN;
        } else if IsPositive(x1) {
            // result is Infinity
            assert DivideFloat(x1, x2) == Infinity;
            assert DivideFloat(x1, x2).Infinity?;
        } else {
            // result is NegInfinity
            assert DivideFloat(x1, x2) == NegInfinity;
            assert DivideFloat(x1, x2).NegInfinity?;
        }
    } else if x1.Infinity? {
        // Case 4: x1 is infinity, x2 is finite non-zero
        assert OptionallyFinite(DivideFloat(x1, x2));
    } else if x1.NegInfinity? {
        // Case 5: x1 is negative infinity, x2 is finite non-zero
        assert OptionallyFinite(DivideFloat(x1, x2));
    } else if x1.Finite? && x2.Finite? {
        // Case 6: Both are finite and x2 is not zero
        assert OptionallyFinite(DivideFloat(x1, x2));
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
  /* code modified by LLM (iteration 5): Complete implementation with proper postcondition verification */
  result := [];
  var i := 0;
  while i < |x1|
    invariant i <= |x1|
    invariant |result| == i
    invariant forall j :: 0 <= j < i ==> result[j] == DivideFloat(x1[j], x2[j])
    invariant forall j :: 0 <= j < i && !IsZero(x2[j]) && x1[j].Finite? && x2[j].Finite? ==> result[j].Finite? && result[j].value == x1[j].value / x2[j].value
    invariant forall j :: 0 <= j < i && !IsZero(x2[j]) && x1[j].Finite? && x2[j].Finite? && result[j].Finite? ==> result[j].value * x2[j].value == x1[j].value
    invariant forall j :: 0 <= j < i && IsZero(x2[j]) && !IsZero(x1[j]) ==> result[j].Infinity? || result[j].NegInfinity?
    invariant forall j :: 0 <= j < i && IsZero(x2[j]) && IsZero(x1[j]) ==> result[j].NaN?
  {
    var div_result := DivideFloat(x1[i], x2[i]);
    DivisionProperties(x1[i], x2[i]);
    result := result + [div_result];
    i := i + 1;
  }
}
// </vc-code>
