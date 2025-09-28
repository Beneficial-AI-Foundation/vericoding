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
{
  /* helper modified by LLM (iteration 3): finite division yields Finite with exact value */
  lemma DivideFloat_finite_when_both_finite_nonzero(x1: FloatValue, x2: FloatValue)
    requires x1.Finite? && x2.Finite? && x2.value != 0.0
    ensures (DivideFloat(x1, x2)).Finite? && (DivideFloat(x1, x2)).value == x1.value / x2.value
  {
    assert DivideFloat(x1, x2) == Finite(x1.value / x2.value);
  }

  /* helper modified by LLM (iteration 3): division by zero with finite non-zero dividend yields infinity or negative infinity */
  lemma DivideFloat_zero_division_finite_dividend(x1: FloatValue, x2: FloatValue)
    requires x2.Finite? && x1.Finite? && x2.value == 0.0 && x1.value != 0.0
    ensures DivideFloat(x1, x2).Infinity? || DivideFloat(x1, x2).NegInfinity?
  {
    if x1.value > 0.0 {
      assert DivideFloat(x1, x2) == Infinity;
    } else {
      assert DivideFloat(x1, x2) == NegInfinity;
    }
  }

  /* helper modified by LLM (iteration 3): zero divided by zero yields NaN */
  lemma DivideFloat_zero_zero(x1: FloatValue, x2: FloatValue)
    requires x1.Finite? && x2.Finite? && x1.value == 0.0 && x2.value == 0.0
    ensures DivideFloat(x1, x2).NaN?
  {
    assert DivideFloat(x1, x2) == NaN;
  }

  /* helper modified by LLM (iteration 3): infinite dividend with zero divisor yields an infinity (proof allows either sign) */
  lemma DivideFloat_zero_division_infinite_dividend(x1: FloatValue, x2: FloatValue)
    requires (x1.Infinity? || x1.NegInfinity?) && IsZero(x2)
    ensures DivideFloat(x1, x2).Infinity? || DivideFloat(x1, x2).NegInfinity?
  {
    // For non-finite infinite dividends and a finite zero divisor, the DivideFloat implementation
    // takes the IsZero(x2) branch and returns either Infinity or NegInfinity. Concretely, it
    // results in NegInfinity in the current definition, which is sufficient for the postcondition.
    if x1.Infinity? {
      assert DivideFloat(x1, x2) == NegInfinity;
    } else {
      assert x1.NegInfinity?;
      assert DivideFloat(x1, x2) == NegInfinity;
    }
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
  /* code modified by LLM (iteration 3): element-wise division with case handling including infinite dividend */
  var i := 0;
  result := [];
  while i < |x1|
    invariant 0 <= i <= |x1|;
    invariant |result| == i;
    invariant forall j :: 0 <= j < |result| ==> result[j] == DivideFloat(x1[j], x2[j]);
  {
    result := result + [DivideFloat(x1[i], x2[i])];
    i := i + 1;
  }

  // Help the verifier by discharging the quantified ensures element-wise using helper lemmas
  var k := 0;
  while k < |result|
    invariant 0 <= k <= |result|;
  {
    // Case: both operands finite and divisor non-zero
    if !IsZero(x2[k]) && x1[k].Finite? && x2[k].Finite? {
      DivideFloat_finite_when_both_finite_nonzero(x1[k], x2[k]);
      assert result[k].Finite? && result[k].value == x1[k].value / x2[k].value;
      assert result[k].value * x2[k].value == x1[k].value;
    }

    // Cases when divisor is zero
    if IsZero(x2[k]) {
      if x1[k].Finite? {
        if x1[k].value == 0.0 {
          // 0 / 0 -> NaN
          DivideFloat_zero_zero(x1[k], x2[k]);
          assert result[k].NaN?;
        } else {
          // finite non-zero dividend / 0 -> +/- Infinity
          DivideFloat_zero_division_finite_dividend(x1[k], x2[k]);
          assert result[k].Infinity? || result[k].NegInfinity?;
        }
      } else if x1[k].Infinity? || x1[k].NegInfinity? {
        // infinite dividend / 0 -> +/- Infinity (as per implementation)
        DivideFloat_zero_division_infinite_dividend(x1[k], x2[k]);
        assert result[k].Infinity? || result[k].NegInfinity?;
      }
    }

    k := k + 1;
  }
}

// </vc-code>
