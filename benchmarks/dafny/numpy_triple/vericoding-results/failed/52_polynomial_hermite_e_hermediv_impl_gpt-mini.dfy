// <vc-preamble>
// Helper predicate to check if a polynomial (coefficient sequence) is non-zero
predicate IsNonZeroPoly(coeffs: seq<real>)
{
    |coeffs| > 0 && exists i :: 0 <= i < |coeffs| && coeffs[i] != 0.0
}

// Helper function to compute the degree of a polynomial represented by coefficients
function PolyDegree(coeffs: seq<real>): int
{
    if |coeffs| == 0 then -1
    else |coeffs| - 1
}

// Helper predicate for well-formed coefficient sequences (no NaN/infinite values)
predicate IsWellFormedCoeffs(coeffs: seq<real>)
{
    forall i :: 0 <= i < |coeffs| ==> coeffs[i] == coeffs[i] // not NaN
}

// Mathematical abstraction for Hermite polynomial evaluation at a point
// This is a ghost function used only in specifications
ghost function EvalHermitePoly(coeffs: seq<real>, x: real): real

// Helper functions for polynomial arithmetic (ghost functions for specification)
ghost function ScalePolyCoeffs(coeffs: seq<real>, scalar: real): seq<real>
{
    seq(|coeffs|, i requires 0 <= i < |coeffs| => coeffs[i] * scalar)
}

ghost function AddPolyCoeffs(c1: seq<real>, c2: seq<real>): seq<real>
{
    var maxLen := if |c1| > |c2| then |c1| else |c2|;
    seq(maxLen, i requires 0 <= i < maxLen => 
        (if i < |c1| then c1[i] else 0.0) + (if i < |c2| then c2[i] else 0.0))
}

ghost function MulPolyCoeffs(c1: seq<real>, c2: seq<real>): seq<real>
{
    if |c1| == 0 || |c2| == 0 then []
    else
        var resultLen := |c1| + |c2| - 1;
        seq(resultLen, k requires 0 <= k < resultLen => 
            (var sum := 0.0;
             sum)) // Simplified for compilation
}

// Axiom: Linear combination property for Hermite polynomial evaluation
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): pad coefficients with zeros to desired length */
function PadZeros(coeffs: seq<real>, newLen: int): seq<real>
  requires newLen >= 0
  ensures |result| == newLen
  ensures forall i :: 0 <= i < |coeffs| && i < newLen ==> result[i] == coeffs[i]
  ensures forall i :: |coeffs| <= i < newLen ==> result[i] == 0.0
{
  seq(newLen, i => if i < |coeffs| then coeffs[i] else 0.0)
}
// </vc-helpers>

// <vc-spec>
lemma {:axiom} HermiteLinearityLemma(c1: seq<real>, c2: seq<real>, a: real, b: real, x: real)
    ensures EvalHermitePoly(AddPolyCoeffs(ScalePolyCoeffs(c1, a), ScalePolyCoeffs(c2, b)), x) == 
            a * EvalHermitePoly(c1, x) + b * EvalHermitePoly(c2, x)

method HermiteDiv(c1: seq<real>, c2: seq<real>) returns (quo: seq<real>, rem: seq<real>)
    requires |c1| >= 0 && |c2| >= 1  // Input dimensions
    requires IsNonZeroPoly(c2)        // Divisor must be non-zero
    requires IsWellFormedCoeffs(c1) && IsWellFormedCoeffs(c2)  // No NaN/infinite coefficients
    
    ensures IsWellFormedCoeffs(quo) && IsWellFormedCoeffs(rem)  // Output well-formedness
    
    // Quotient dimension constraint: max(|c1| - |c2|, 0) + 1 for proper polynomial division
    ensures |quo| == if |c1| >= |c2| then |c1| - |c2| + 1 else 1
    
    // Remainder dimension constraint: degree less than divisor degree
    ensures |rem| == |c2| - 1
    
    // Fundamental division identity: c1 = quo * c2 + rem (as Hermite polynomials)
    // This captures the mathematical correctness of polynomial division
    ensures forall x :: EvalHermitePoly(c1, x) == 
                       EvalHermitePoly(AddPolyCoeffs(MulPolyCoeffs(quo, c2), rem), x)
    
    // Degree constraint: remainder degree < divisor degree (fundamental division property)
    ensures PolyDegree(rem) < PolyDegree(c2) || (|rem| == 0)
    
    // Non-degeneracy: if dividend degree >= divisor degree, quotient is non-trivial
    ensures |c1| >= |c2| ==> |quo| >= 1
    
    // Boundary case: if dividend degree < divisor degree, quotient should be minimal
    ensures |c1| < |c2| ==> |quo| == 1
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): polynomial long division producing quotient and remainder */
  if |c1| < |c2| {
    quo := seq(1, i => 0.0);
    rem := PadZeros(c1, |c2| - 1);
    return;
  }

  var n1 := |c1|;
  var n2 := |c2|;
  var qlen := n1 - n2 + 1;

  // initialize working array r with coefficients of c1
  var r := new real[n1];
  var i := 0;
  while i < n1
    invariant 0 <= i <= n1
    invariant forall t :: 0 <= t < i ==> r[t] == c1[t]
    decreases n1 - i
  {
    r[i] := c1[i];
    i := i + 1;
  }

  var qarr := new real[qlen];
  var kk := qlen;
  var lc := c2[n2 - 1];
  while kk > 0
    invariant 0 <= kk <= qlen
    decreases kk
  {
    var idx := kk - 1;
    var factor := r[n2 - 1 + idx] / lc;
    qarr[idx] := factor;
    var j := 0;
    while j < n2
      invariant 0 <= j <= n2
      decreases n2 - j
    {
      r[j + idx] := r[j + idx] - factor * c2[j];
      j := j + 1;
    }
    kk := kk - 1;
  }

  quo := qarr[..];
  rem := seq(n2 - 1, k => r[k]);
}
// </vc-code>
