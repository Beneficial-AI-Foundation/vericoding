// <vc-preamble>
datatype FloatValue = 
  | Finite(value: real)
  | PosInf
  | NegInf  
  | NaN

// Predicate to test if a FloatValue is negative infinity
predicate IsNegInf(f: FloatValue)
{
  f.NegInf?
}

// Predicate to test if a FloatValue is any kind of infinity
predicate IsInf(f: FloatValue)
{
  f.PosInf? || f.NegInf?
}

// Predicate to test if a FloatValue is NaN
predicate IsNaN(f: FloatValue)
{
  f.NaN?
}

// Predicate to test if a FloatValue is finite
predicate IsFinite(f: FloatValue)
{
  f.Finite?
}

// Predicate to test if a FloatValue is zero
predicate IsZero(f: FloatValue)
{
  f.Finite? && f.value == 0.0
}
// </vc-preamble>

// <vc-helpers>
lemma FiniteNotNegInf(f: FloatValue)
  ensures f.Finite? ==> !f.NegInf?
{
  match f {
    case Finite(_) => assert !f.NegInf?;
    case _ => {}
  }
}

lemma PosInfNotNegInf(f: FloatValue)
  ensures f.PosInf? ==> !f.NegInf?
{
  match f {
    case PosInf => assert !f.NegInf?;
    case _ => {}
  }
}

lemma IsNaNNotNegInf(f: FloatValue)
  ensures IsNaN(f) ==> !f.NegInf?
{
  match f {
    case NaN => assert !f.NegInf?;
    case _ => {}
  }
}

lemma NegInfNotNaN(f: FloatValue)
  ensures f.NegInf? ==> !IsNaN(f)
{
  match f {
    case NegInf => assert !IsNaN(f);
    case _ => {}
  }
}

lemma NegInfNotFinite(f: FloatValue)
  ensures f.NegInf? ==> !f.Finite?
{
  match f {
    case NegInf => assert !f.Finite?;
    case _ => {}
  }
}

lemma NegInfNotPosInf(f: FloatValue)
  ensures f.NegInf? ==> !f.PosInf?
{
  match f {
    case NegInf => assert !f.PosInf?;
    case _ => {}
  }
}

// </vc-helpers>

// <vc-spec>
method CheckNegInf(x: array<FloatValue>) returns (result: array<bool>)
  // Output array has same length as input
  ensures result.Length == x.Length
  // Primary property: result[i] is true iff x[i] is negative infinity
  ensures forall i :: 0 <= i < result.Length ==> 
    (result[i] <==> IsNegInf(x[i]))
  // Finite values return false  
  ensures forall i :: 0 <= i < result.Length ==> 
    (IsFinite(x[i]) ==> !result[i])
  // Positive infinity returns false
  ensures forall i :: 0 <= i < result.Length ==> 
    (x[i].PosInf? ==> !result[i])
  // NaN returns false
  ensures forall i :: 0 <= i < result.Length ==> 
    (IsNaN(x[i]) ==> !result[i])
  // Zero returns false
  ensures forall i :: 0 <= i < result.Length ==> 
    (IsZero(x[i]) ==> !result[i])
  // If result is true, then input is negative infinity
  ensures forall i :: 0 <= i < result.Length ==> 
    (result[i] ==> x[i].NegInf?)
  // Exclusivity: cannot be both negative infinity and NaN
  ensures forall i :: 0 <= i < result.Length ==> 
    (result[i] ==> !IsNaN(x[i]))
  // Exclusivity: cannot be both negative infinity and finite
  ensures forall i :: 0 <= i < result.Length ==> 
    (result[i] ==> !IsFinite(x[i]))
  // Exclusivity: cannot be both negative infinity and positive infinity
  ensures forall i :: 0 <= i < result.Length ==> 
    (result[i] ==> !x[i].PosInf?)
// </vc-spec>
// <vc-code>
{
  var n := x.Length;
  result := new bool[n];
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant result.Length == n
    invariant forall j :: 0 <= j < i ==> (result[j] <==> IsNegInf(x[j]))
  {
    result[i] := IsNegInf(x[i]);
    i := i + 1;
  }
}

// </vc-code>
