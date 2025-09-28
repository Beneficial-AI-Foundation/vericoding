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
/* helper modified by LLM (iteration 2): use datatype tag disjointness to show finite is not -inf */
lemma FiniteImplNotNegInf(f: FloatValue)
  ensures IsFinite(f) ==> !IsNegInf(f)
{
}

/* helper modified by LLM (iteration 2): show +inf is not -inf */
lemma PosInfImplNotNegInf(f: FloatValue)
  ensures f.PosInf? ==> !IsNegInf(f)
{
}

/* helper modified by LLM (iteration 2): show NaN is not -inf */
lemma NaNImplNotNegInf(f: FloatValue)
  ensures IsNaN(f) ==> !IsNegInf(f)
{
}

/* helper modified by LLM (iteration 2): zero (finite 0) is not -inf */
lemma ZeroImplNotNegInf(f: FloatValue)
  ensures IsZero(f) ==> !IsNegInf(f)
{
}

/* helper modified by LLM (iteration 2): restate predicate definition */
lemma NegInfImplTag(f: FloatValue)
  ensures IsNegInf(f) ==> f.NegInf?
{
}

/* helper modified by LLM (iteration 2): exclusivity with finite */
lemma NegInfImplNotFinite(f: FloatValue)
  ensures IsNegInf(f) ==> !IsFinite(f)
{
}

/* helper modified by LLM (iteration 2): exclusivity with NaN */
lemma NegInfImplNotNaN(f: FloatValue)
  ensures IsNegInf(f) ==> !IsNaN(f)
{
}

/* helper modified by LLM (iteration 2): exclusivity with +inf */
lemma NegInfImplNotPosInf(f: FloatValue)
  ensures IsNegInf(f) ==> !f.PosInf?
{
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
  /* code modified by LLM (iteration 2): simple loop to compute NegInf flags; removed trivial null invariant to avoid warning */
  var n := x.Length;
  result := new bool[n];
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant result.Length == n
    invariant forall j :: 0 <= j < i ==> (result[j] <==> IsNegInf(x[j]))
    decreases n - i
  {
    result[i] := IsNegInf(x[i]);
    i := i + 1;
  }
}
// </vc-code>
