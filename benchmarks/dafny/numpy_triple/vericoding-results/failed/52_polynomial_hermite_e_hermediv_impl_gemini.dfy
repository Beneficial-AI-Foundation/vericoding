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
/* helper modified by LLM (iteration 4): [no change needed, helper is correct] */
function TrueDegree(p: seq<real>): int
    decreases |p|
{
    if |p| == 0 then -1
    else if p[|p|-1] != 0.0 then |p|-1
    else TrueDegree(p[..|p|-1])
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
  /* code modified by LLM (iteration 4): [converted for loop to while loop and fixed initialization] */
    // Find the true degree and leading coefficient of the divisor c2.
    var m_deg := TrueDegree(c2);
    assert m_deg >= 0; // from requires IsNonZeroPoly(c2)
    var c2_trimmed := c2[..m_deg+1];
    var m_trimmed := |c2_trimmed|;
    var lc2 := c2_trimmed[m_trimmed-1];
    assert lc2 != 0.0;

    // Find the true degree of the dividend c1.
    var n_deg := TrueDegree(c1);
    var c1_trimmed := if n_deg == -1 then [] else c1[..n_deg+1];
    var n_trimmed := |c1_trimmed|;
    
    // Determine output array sizes from specs
    var q_len_out := if |c1| >= |c2| then |c1| - |c2| + 1 else 1;
    var r_len_out := |c2| - 1;

    if n_trimmed < m_trimmed { // True degree of c1 < true degree of c2
        quo := seq(q_len_out, _ => 0.0);
        var rem_arr := new real[r_len_out];
        for k := 0 to r_len_out - 1 {
            rem_arr[k] := if k < |c1| then c1[k] else 0.0;
        }
        rem := rem_arr[..];
        return;
    }

    // Perform long division using true degrees
    var q_len_calc := n_trimmed - m_trimmed + 1;
    var q_mut := new real[q_len_calc];
    for k := 0 to q_len_calc - 1 { q_mut[k] := 0.0; } // Initialize to ensure well-formedness
    
    var r_mut := new real[n_trimmed];
    for k := 0 to n_trimmed-1 { r_mut[k] := c1_trimmed[k]; }
    
    var i := n_trimmed - m_trimmed;
    while i >= 0
        invariant -1 <= i <= n_trimmed - m_trimmed
        invariant IsWellFormedCoeffs(q_mut[..])
        invariant IsWellFormedCoeffs(r_mut[..])
        decreases i
    {
        var scale := r_mut[i + m_trimmed - 1] / lc2;
        q_mut[i] := scale;
        for j := 0 to m_trimmed - 1 {
            r_mut[i+j] := r_mut[i+j] - scale * c2_trimmed[j];
        }
        i := i - 1;
    }

    // Format quotient to the required output length
    var quo_arr := new real[q_len_out];
    for k := 0 to q_len_out-1 {
        quo_arr[k] := if k < q_len_calc then q_mut[k] else 0.0;
    }
    quo := quo_arr[..];

    // Format remainder to the required output length
    var rem_arr := new real[r_len_out];
    var r_deg_final := TrueDegree(r_mut[..m_trimmed-1]);
    for k := 0 to r_len_out-1 {
        rem_arr[k] := if k <= r_deg_final then r_mut[k] else 0.0;
    }
    rem := rem_arr[..];
}
// </vc-code>
