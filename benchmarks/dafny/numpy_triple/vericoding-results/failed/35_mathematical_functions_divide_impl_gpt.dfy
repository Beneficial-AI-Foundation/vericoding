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
/* helper modified by LLM (iteration 5): real arithmetic cancellation (division then multiplication) */
lemma MultDivCancel(a: real, b: real)
    requires b != 0.0
    ensures (a / b) * b == a
{
  assert (a / b) * b == a;
}

/* helper modified by LLM (iteration 5): when both operands are finite and denominator non-zero, DivideFloat yields the exact finite quotient */
lemma DivideFloat_FiniteNonZeroDenomEquality(x1: FloatValue, x2: FloatValue)
    requires x1.Finite? && x2.Finite?
    requires !IsZero(x2)
    ensures DivideFloat(x1, x2).Finite?
    ensures DivideFloat(x1, x2).value == x1.value / x2.value
{
  assert !x1.NaN? && !x2.NaN?;
  assert !x2.Infinity? && !x2.NegInfinity?;
  assert !IsZero(x2);
  assert !x1.Infinity? && !x1.NegInfinity?;
  assert x1.Finite? && x2.Finite?;
  assert DivideFloat(x1, x2) == Finite(x1.value / x2.value);
}

/* helper modified by LLM (iteration 5): dividing by zero with a finite non-zero numerator results in an infinity */
lemma DivideFloat_ZeroDenom_FiniteNumerator(x1: FloatValue, x2: FloatValue)
    requires IsZero(x2)
    requires x1.Finite?
    requires !IsZero(x1)
    ensures DivideFloat(x1, x2).Infinity? || DivideFloat(x1, x2).NegInfinity?
{
  assert x1.value != 0.0;
  if x1.value > 0.0 {
    assert IsPositive(x1);
    assert DivideFloat(x1, x2) == Infinity;
  } else {
    assert x1.value < 0.0;
    assert IsNegative(x1);
    assert DivideFloat(x1, x2) == NegInfinity;
  }
}

/* helper modified by LLM (iteration 5): dividing by zero with infinite numerator selects NegInfinity per DivideFloat definition */
lemma DivideFloat_ZeroDenom_InfiniteNumerator(x1: FloatValue, x2: FloatValue)
    requires IsZero(x2)
    requires x1.Infinity? || x1.NegInfinity?
    ensures DivideFloat(x1, x2).Infinity? || DivideFloat(x1, x2).NegInfinity?
{
  assert !IsZero(x1);
  assert !IsPositive(x1);
  assert DivideFloat(x1, x2) == NegInfinity;
}

/* helper modified by LLM (iteration 5): dividing zero by zero results in NaN */
lemma DivideFloat_ZeroOverZeroIsNaN(x1: FloatValue, x2: FloatValue)
    requires IsZero(x1) && IsZero(x2)
    ensures DivideFloat(x1, x2).NaN?
{
  assert DivideFloat(x1, x2) == NaN;
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
  /* code modified by LLM (iteration 5): element-wise division with invariants and case analyses for zero/non-zero denominators */
  var r: seq<FloatValue> := [];
  var i := 0;
  while i < |x1|
    invariant 0 <= i <= |x1|
    invariant |r| == i
    invariant forall j :: 0 <= j < i ==> r[j] == DivideFloat(x1[j], x2[j])
    invariant forall j :: 0 <= j < i && !IsZero(x2[j]) && x1[j].Finite? && x2[j].Finite? ==> r[j].Finite? && r[j].value == x1[j].value / x2[j].value
    invariant forall j :: 0 <= j < i && !IsZero(x2[j]) && x1[j].Finite? && x2[j].Finite? && r[j].Finite? ==> r[j].value * x2[j].value == x1[j].value
    invariant forall j :: 0 <= j < i && IsZero(x2[j]) && !IsZero(x1[j]) ==> r[j].Infinity? || r[j].NegInfinity?
    invariant forall j :: 0 <= j < i && IsZero(x2[j]) && IsZero(x1[j]) ==> r[j].NaN?
  {
    var d := DivideFloat(x1[i], x2[i]);

    if !IsZero(x2[i]) && x1[i].Finite? && x2[i].Finite? {
      DivideFloat_FiniteNonZeroDenomEquality(x1[i], x2[i]);
      assert d.Finite?;
      assert d.value == x1[i].value / x2[i].value;
      assert x2[i].value != 0.0;
      MultDivCancel(x1[i].value, x2[i].value);
      assert d.value * x2[i].value == x1[i].value;
    }

    if IsZero(x2[i]) {
      if IsZero(x1[i]) {
        DivideFloat_ZeroOverZeroIsNaN(x1[i], x2[i]);
        assert d.NaN?;
      } else {
        if x1[i].Finite? {
          DivideFloat_ZeroDenom_FiniteNumerator(x1[i], x2[i]);
          assert d.Infinity? || d.NegInfinity?;
        } else if x1[i].Infinity? || x1[i].NegInfinity? {
          DivideFloat_ZeroDenom_InfiniteNumerator(x1[i], x2[i]);
          assert d.Infinity? || d.NegInfinity?;
        }
      }
    }

    r := r + [d];
    i := i + 1;
  }
  result := r;
}
// </vc-code>
