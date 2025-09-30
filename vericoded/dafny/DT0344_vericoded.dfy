// <vc-preamble>
// Looking at the errors, the main issue is with the sequence comprehension syntax on line 64. Dafny's sequence comprehension syntax doesn't support the filter-like syntax being used. I'll fix this by providing a proper sequence construction approach.



// Custom datatype to represent floating point values including NaN and infinities
datatype FloatValue = 
  | Finite(value: real)
  | PosInf
  | NegInf  
  | NaN

// Helper predicates for FloatValue
predicate IsNaN(f: FloatValue) {
  f.NaN?
}

predicate IsFinite(f: FloatValue) {
  f.Finite?
}

predicate IsPositiveInfinity(f: FloatValue) {
  f.PosInf?
}

predicate IsNegativeInfinity(f: FloatValue) {
  f.NegInf?
}

// Helper function to get numeric value for comparison (treating infinities as extreme values)
function GetComparisonValue(f: FloatValue): real
  requires !IsNaN(f)
{
  match f
    case Finite(v) => v
    case PosInf => 1000000.0  // Represent as large positive value
    case NegInf => -1000000.0 // Represent as large negative value
}

// Helper predicate for positive values
predicate IsPositive(f: FloatValue) {
  f.PosInf? || (f.Finite? && f.value > 0.0)
}

// Helper predicate for negative values  
predicate IsNegative(f: FloatValue) {
  f.NegInf? || (f.Finite? && f.value < 0.0)
}

// FloatValue addition with NaN and infinity semantics
function AddFloat(a: FloatValue, b: FloatValue): FloatValue {
  if IsNaN(a) || IsNaN(b) then NaN
  else if IsPositiveInfinity(a) && IsNegativeInfinity(b) then NaN
  else if IsNegativeInfinity(a) && IsPositiveInfinity(b) then NaN
  else if IsPositiveInfinity(a) || IsPositiveInfinity(b) then PosInf
  else if IsNegativeInfinity(a) || IsNegativeInfinity(b) then NegInf
  else Finite(a.value + b.value)
}

// Sum a sequence treating NaN as zero
function SumTreatingNaNAsZero(values: seq<FloatValue>): FloatValue {
  if |values| == 0 then Finite(0.0)
  else
    FoldSum(values, 0)
}

// Recursive helper to sum non-NaN values
function FoldSum(values: seq<FloatValue>, index: nat): FloatValue
  decreases |values| - index
{
  if index >= |values| then Finite(0.0)
  else if IsNaN(values[index]) then FoldSum(values, index + 1)
  else AddFloat(values[index], FoldSum(values, index + 1))
}

// Check if sequence contains positive infinity (ignoring NaN)
predicate ContainsPositiveInfinity(values: seq<FloatValue>) {
  exists i :: 0 <= i < |values| && IsPositiveInfinity(values[i])
}

// Check if sequence contains negative infinity (ignoring NaN) 
predicate ContainsNegativeInfinity(values: seq<FloatValue>) {
  exists i :: 0 <= i < |values| && IsNegativeInfinity(values[i])
}

// Check if all values are NaN
predicate AllValuesAreNaN(values: seq<FloatValue>) {
  forall i :: 0 <= i < |values| ==> IsNaN(values[i])
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): Strengthened BothInfImpliesNaNSum lemma to properly prove NaN result */

// Lemma to prove that if all values are NaN, the sum is 0
lemma AllNaNImpliesZeroSum(values: seq<FloatValue>)
  requires AllValuesAreNaN(values)
  ensures SumTreatingNaNAsZero(values) == Finite(0.0)
{
  if |values| == 0 {
    // Base case: empty sequence
  } else {
    // Inductive case
    AllNaNImpliesZeroSumHelper(values, 0);
  }
}

lemma AllNaNImpliesZeroSumHelper(values: seq<FloatValue>, index: nat)
  requires AllValuesAreNaN(values)
  requires index <= |values|
  ensures FoldSum(values, index) == Finite(0.0)
  decreases |values| - index
{
  if index >= |values| {
    // Base case
  } else {
    assert IsNaN(values[index]);
    AllNaNImpliesZeroSumHelper(values, index + 1);
  }
}

// Lemma for positive infinity only
lemma PosInfOnlyImpliesPosInfSum(values: seq<FloatValue>)
  requires ContainsPositiveInfinity(values)
  requires !ContainsNegativeInfinity(values)
  requires !AllValuesAreNaN(values)
  ensures SumTreatingNaNAsZero(values) == PosInf
{
  if |values| > 0 {
    var posIdx :| 0 <= posIdx < |values| && IsPositiveInfinity(values[posIdx]);
    PosInfOnlyImpliesPosInfSumHelper(values, 0, posIdx);
  }
}

lemma PosInfOnlyImpliesPosInfSumHelper(values: seq<FloatValue>, index: nat, posIdx: nat)
  requires 0 <= posIdx < |values| && IsPositiveInfinity(values[posIdx])
  requires !ContainsNegativeInfinity(values)
  requires index <= |values|
  ensures index <= posIdx < |values| ==> FoldSum(values, index) == PosInf
  ensures index > posIdx ==> FoldSum(values, index) == PosInf || FoldSum(values, index).Finite?
  decreases |values| - index
{
  if index >= |values| {
    // Base case
  } else if IsNaN(values[index]) {
    PosInfOnlyImpliesPosInfSumHelper(values, index + 1, posIdx);
  } else if index == posIdx {
    assert IsPositiveInfinity(values[index]);
    PosInfOnlyImpliesPosInfSumHelper(values, index + 1, posIdx);
    var rest := FoldSum(values, index + 1);
    assert AddFloat(PosInf, rest) == PosInf;
  } else {
    PosInfOnlyImpliesPosInfSumHelper(values, index + 1, posIdx);
  }
}

// Lemma for negative infinity only
lemma NegInfOnlyImpliesNegInfSum(values: seq<FloatValue>)
  requires !ContainsPositiveInfinity(values)
  requires ContainsNegativeInfinity(values)
  requires !AllValuesAreNaN(values)
  ensures SumTreatingNaNAsZero(values) == NegInf
{
  if |values| > 0 {
    var negIdx :| 0 <= negIdx < |values| && IsNegativeInfinity(values[negIdx]);
    NegInfOnlyImpliesNegInfSumHelper(values, 0, negIdx);
  }
}

lemma NegInfOnlyImpliesNegInfSumHelper(values: seq<FloatValue>, index: nat, negIdx: nat)
  requires 0 <= negIdx < |values| && IsNegativeInfinity(values[negIdx])
  requires !ContainsPositiveInfinity(values)
  requires index <= |values|
  ensures index <= negIdx < |values| ==> FoldSum(values, index) == NegInf
  ensures index > negIdx ==> FoldSum(values, index) == NegInf || FoldSum(values, index).Finite?
  decreases |values| - index
{
  if index >= |values| {
    // Base case
  } else if IsNaN(values[index]) {
    NegInfOnlyImpliesNegInfSumHelper(values, index + 1, negIdx);
  } else if index == negIdx {
    assert IsNegativeInfinity(values[index]);
    NegInfOnlyImpliesNegInfSumHelper(values, index + 1, negIdx);
    var rest := FoldSum(values, index + 1);
    assert AddFloat(NegInf, rest) == NegInf;
  } else {
    NegInfOnlyImpliesNegInfSumHelper(values, index + 1, negIdx);
  }
}

// Lemma for both infinities - properly proves NaN result
lemma BothInfImpliesNaNSum(values: seq<FloatValue>)
  requires ContainsPositiveInfinity(values)
  requires ContainsNegativeInfinity(values)
  requires !AllValuesAreNaN(values)
  ensures SumTreatingNaNAsZero(values) == NaN
{
  if |values| > 0 {
    var posIdx :| 0 <= posIdx < |values| && IsPositiveInfinity(values[posIdx]);
    var negIdx :| 0 <= negIdx < |values| && IsNegativeInfinity(values[negIdx]);
    assert posIdx != negIdx;
    BothInfImpliesNaNSumHelper(values, 0, posIdx, negIdx);
  }
}

lemma BothInfImpliesNaNSumHelper(values: seq<FloatValue>, index: nat, posIdx: nat, negIdx: nat)
  requires 0 <= posIdx < |values| && IsPositiveInfinity(values[posIdx])
  requires 0 <= negIdx < |values| && IsNegativeInfinity(values[negIdx])
  requires posIdx != negIdx
  requires index <= |values|
  ensures (index <= posIdx < |values| && index <= negIdx < |values|) ==> FoldSum(values, index) == NaN
  ensures (index <= posIdx < |values| && index > negIdx) ==> FoldSum(values, index) == PosInf || FoldSum(values, index) == NaN
  ensures (index > posIdx && index <= negIdx < |values|) ==> FoldSum(values, index) == NegInf || FoldSum(values, index) == NaN
  decreases |values| - index
{
  if index >= |values| {
    // Base case
  } else if IsNaN(values[index]) {
    BothInfImpliesNaNSumHelper(values, index + 1, posIdx, negIdx);
  } else if index == posIdx {
    assert IsPositiveInfinity(values[index]);
    if negIdx > index {
      BothInfImpliesNaNSumHelper(values, index + 1, posIdx, negIdx);
      var rest := FoldSum(values, index + 1);
      if rest == NegInf {
        assert AddFloat(PosInf, NegInf) == NaN;
      }
    } else {
      BothInfImpliesNaNSumHelper(values, index + 1, posIdx, negIdx);
    }
  } else if index == negIdx {
    assert IsNegativeInfinity(values[index]);
    if posIdx > index {
      BothInfImpliesNaNSumHelper(values, index + 1, posIdx, negIdx);
      var rest := FoldSum(values, index + 1);
      if rest == PosInf {
        assert AddFloat(NegInf, PosInf) == NaN;
      }
    } else {
      BothInfImpliesNaNSumHelper(values, index + 1, posIdx, negIdx);
    }
  } else {
    BothInfImpliesNaNSumHelper(values, index + 1, posIdx, negIdx);
  }
}
// </vc-helpers>

// <vc-spec>
method nansum(a: seq<FloatValue>) returns (result: FloatValue)
  ensures 
    // Core specification: result is the fold sum treating NaN as zero
    result == SumTreatingNaNAsZero(a) &&
    
    // If empty sequence, result is 0
    (|a| == 0 ==> result == Finite(0.0)) &&
    
    // If all elements are NaN, result is 0  
    (AllValuesAreNaN(a) ==> result == Finite(0.0)) &&
    
    // If both positive and negative infinity present (and not all NaN), result is NaN
    (ContainsPositiveInfinity(a) && ContainsNegativeInfinity(a) && !AllValuesAreNaN(a) 
     ==> IsNaN(result)) &&
    
    // If only positive infinity present (and not all NaN), result is positive infinity
    (ContainsPositiveInfinity(a) && !ContainsNegativeInfinity(a) && !AllValuesAreNaN(a)
     ==> IsPositiveInfinity(result)) &&
    
    // If only negative infinity present (and not all NaN), result is negative infinity  
    (!ContainsPositiveInfinity(a) && ContainsNegativeInfinity(a) && !AllValuesAreNaN(a)
     ==> IsNegativeInfinity(result))
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 4): Call SumTreatingNaNAsZero and invoke lemmas to prove postconditions */
  result := SumTreatingNaNAsZero(a);
  
  // Apply appropriate lemma based on the conditions
  if AllValuesAreNaN(a) {
    AllNaNImpliesZeroSum(a);
  } else if ContainsPositiveInfinity(a) && ContainsNegativeInfinity(a) {
    BothInfImpliesNaNSum(a);
  } else if ContainsPositiveInfinity(a) && !ContainsNegativeInfinity(a) {
    PosInfOnlyImpliesPosInfSum(a);
  } else if !ContainsPositiveInfinity(a) && ContainsNegativeInfinity(a) {
    NegInfOnlyImpliesNegInfSum(a);
  }
}
// </vc-code>
