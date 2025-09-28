// <vc-preamble>
// Built-in trigonometric functions - assumed to be available
function {:extern} Sin(x: real): real
function {:extern} Arcsin(x: real): real

// Mathematical constants
const PI: real := 3.141592653589793
const HALF_PI: real := 1.5707963267948966

// Specification for the inverse relationship between sin and arcsin
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): per-index arcsin properties */
lemma Arcsin_Properties_For_Index(x: seq<real>, i: int)
  requires 0 <= i < |x|
  requires -1.0 <= x[i] <= 1.0
  ensures -HALF_PI <= Arcsin(x[i]) <= HALF_PI
  ensures Sin(Arcsin(x[i])) == x[i]
  ensures x[i] == 0.0 ==> Arcsin(x[i]) == 0.0
  ensures x[i] == 1.0 ==> Arcsin(x[i]) == HALF_PI
  ensures x[i] == -1.0 ==> Arcsin(x[i]) == -HALF_PI
{
  Arcsin_Range(x[i]);
  SinArcsin_Inverse(x[i]);
  if x[i] == 0.0 {
    Arcsin_SpecialValues();
    assert Arcsin(0.0) == 0.0;
    assert Arcsin(x[i]) == 0.0;
  } else if x[i] == 1.0 {
    Arcsin_SpecialValues();
    assert Arcsin(1.0) == HALF_PI;
    assert Arcsin(x[i]) == HALF_PI;
  } else if x[i] == -1.0 {
    Arcsin_SpecialValues();
    assert Arcsin(-1.0) == -HALF_PI;
    assert Arcsin(x[i]) == -HALF_PI;
  }
}

/* helper modified by LLM (iteration 5): monotonicity for two indices in a sequence */
lemma Arcsin_Seq_Monotonic(x: seq<real>, i: int, j: int)
  requires 0 <= i < |x|
  requires 0 <= j < |x|
  requires -1.0 <= x[i] <= 1.0
  requires -1.0 <= x[j] <= 1.0
  requires x[i] <= x[j]
  ensures Arcsin(x[i]) <= Arcsin(x[j])
{
  Arcsin_Monotonic(x[i], x[j]);
}

/* helper modified by LLM (iteration 5): array-level monotonicity from per-index equality */
lemma Array_Arcsin_Monotonic(a: array<real>, x: seq<real>)
  requires a.Length == |x|
  requires forall k :: 0 <= k < |x| ==> -1.0 <= x[k] <= 1.0
  requires forall k :: 0 <= k < |x| ==> a[k] == Arcsin(x[k])
  ensures forall p,q :: 0 <= p < |x| && 0 <= q < |x| && x[p] <= x[q] ==> a[p] <= a[q]
{
  var p := 0;
  while p < |x|
    invariant 0 <= p <= |x|
    invariant forall p', q :: 0 <= p' < p && 0 <= q < |x| && x[p'] <= x[q] ==> a[p'] <= a[q]
  {
    var q := 0;
    while q < |x|
      invariant 0 <= q <= |x|
      invariant forall q' :: 0 <= q' < q && x[p] <= x[q'] ==> a[p] <= a[q']
      invariant forall p', q' :: 0 <= p' < p && 0 <= q' < |x| && x[p'] <= x[q'] ==> a[p'] <= a[q']
    {
      if x[p] <= x[q] {
        Arcsin_Monotonic(x[p], x[q]);
        assert a[p] == Arcsin(x[p]);
        assert a[q] == Arcsin(x[q]);
        assert Arcsin(x[p]) <= Arcsin(x[q]);
        assert a[p] <= a[q];
      }
      q := q + 1;
    }
    p := p + 1;
  }
}

// </vc-helpers>

// <vc-spec>
lemma {:axiom} SinArcsin_Inverse(x: real)
  requires -1.0 <= x <= 1.0
  ensures Sin(Arcsin(x)) == x

// Specification for arcsin range
lemma {:axiom} Arcsin_Range(x: real)
  requires -1.0 <= x <= 1.0
  ensures -HALF_PI <= Arcsin(x) <= HALF_PI

// Specification for arcsin monotonicity
lemma {:axiom} Arcsin_Monotonic(x: real, y: real)
  requires -1.0 <= x <= 1.0
  requires -1.0 <= y <= 1.0
  requires x <= y
  ensures Arcsin(x) <= Arcsin(y)

// Specification for special values
lemma {:axiom} Arcsin_SpecialValues()
  ensures Arcsin(0.0) == 0.0
  ensures Arcsin(1.0) == HALF_PI
  ensures Arcsin(-1.0) == -HALF_PI

/**
 * Computes the inverse sine of each element in the input sequence.
 * For real arguments, the domain is [-1, 1] and the range is [-π/2, π/2].
 */
method numpy_arcsin(x: seq<real>) returns (result: seq<real>)
  // Precondition: All elements must be in domain [-1, 1]
  requires forall i :: 0 <= i < |x| ==> -1.0 <= x[i] <= 1.0
  
  // Postcondition: Output has same length as input
  ensures |result| == |x|
  
  // Postcondition: Each element is arcsin of corresponding input element
  ensures forall i :: 0 <= i < |x| ==> result[i] == Arcsin(x[i])
  
  // Postcondition: All results are in valid range [-π/2, π/2]
  ensures forall i :: 0 <= i < |result| ==> -HALF_PI <= result[i] <= HALF_PI
  
  // Postcondition: Inverse relationship holds (sin(arcsin(x)) = x)
  ensures forall i :: 0 <= i < |x| ==> Sin(result[i]) == x[i]
  
  // Postcondition: Monotonicity property
  ensures forall i, j :: 0 <= i < |x| && 0 <= j < |x| && x[i] <= x[j] ==> result[i] <= result[j]
  
  // Postcondition: Special values
  ensures forall i :: 0 <= i < |x| && x[i] == 0.0 ==> result[i] == 0.0
  ensures forall i :: 0 <= i < |x| && x[i] == 1.0 ==> result[i] == HALF_PI
  ensures forall i :: 0 <= i < |x| && x[i] == -1.0 ==> result[i] == -HALF_PI
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): elementwise arcsin with monotonicity proof */
  var a := new real[|x|];
  var i := 0;
  while i < |x|
    invariant 0 <= i <= |x|
    invariant forall k :: 0 <= k < i ==> a[k] == Arcsin(x[k])
    invariant forall k :: 0 <= k < i ==> -HALF_PI <= a[k] <= HALF_PI
    invariant forall k :: 0 <= k < i ==> Sin(a[k]) == x[k]
    invariant forall k :: 0 <= k < i ==> (x[k] == 0.0 ==> a[k] == 0.0)
    invariant forall k :: 0 <= k < i ==> (x[k] == 1.0 ==> a[k] == HALF_PI)
    invariant forall k :: 0 <= k < i ==> (x[k] == -1.0 ==> a[k] == -HALF_PI)
  {
    a[i] := Arcsin(x[i]);
    Arcsin_Properties_For_Index(x, i);
    i := i + 1;
  }
  Array_Arcsin_Monotonic(a, x);
  result := a[..];
}

// </vc-code>
