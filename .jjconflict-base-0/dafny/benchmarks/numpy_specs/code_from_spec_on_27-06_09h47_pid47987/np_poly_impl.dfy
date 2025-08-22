//https://numpy.org/doc/stable/reference/generated/numpy.poly.html

//Find the coefficients of a polynomial with the given sequence of roots.

//IMPL poly
method poly (roots: array<real>) returns (coeff: array<real>)
    requires roots.Length > 0
    ensures coeff.Length == roots.Length + 1
    ensures coeff[0] == 1.0
{
    coeff := new real[roots.Length + 1];
    coeff[0] := 1.0;
    
    /* code modified by LLM (iteration 4): initialize all coefficients to 0 */
    var i := 1;
    while i < roots.Length + 1 
        invariant 1 <= i <= roots.Length + 1
        invariant coeff.Length == roots.Length + 1
        invariant coeff[0] == 1.0
    {
        coeff[i] := 0.0;
        i := i + 1;
    }
    
    /* code modified by LLM (iteration 4): compute polynomial coefficients with corrected logic */
    i := 0;
    while i < roots.Length
        invariant 0 <= i <= roots.Length
        invariant coeff.Length == roots.Length + 1
        invariant coeff[0] == 1.0
    {
        var j := i + 1;
        while j > 0
            invariant 0 <= j <= i + 1
            invariant coeff.Length == roots.Length + 1
            invariant coeff[0] == 1.0
            invariant 0 <= i < roots.Length
            invariant j <= coeff.Length - 1
        {
            coeff[j] := coeff[j] - roots[i] * coeff[j-1];
            j := j - 1;
        }
        i := i + 1;
    }
}

//IMPL poly_helper
method poly_helper (roots: array<real>, val: nat) returns (coeff: array<real>)
    requires roots.Length > 0
    requires val <= roots.Length
    decreases val
    ensures coeff.Length == val + 1
    ensures coeff[0] == 1.0
{
    if val == 0 {
        coeff := new real[1];
        coeff[0] := 1.0;
    } else {
        /* code modified by LLM (iteration 4): ensure recursive call is valid */
        var prev_coeff := poly_helper(roots, val - 1);
        coeff := new real[val + 1];
        
        /* code modified by LLM (iteration 4): initialize all coefficients to 0 first */
        var i := 0;
        while i < val + 1
            invariant 0 <= i <= val + 1
            invariant coeff.Length == val + 1
        {
            coeff[i] := 0.0;
            i := i + 1;
        }
        
        /* code modified by LLM (iteration 4): copy previous coefficients correctly */
        i := 0;
        while i < prev_coeff.Length
            invariant 0 <= i <= prev_coeff.Length
            invariant coeff.Length == val + 1
            invariant prev_coeff.Length == val
            invariant val > 0
        {
            coeff[i] := prev_coeff[i];
            i := i + 1;
        }
        
        /* code modified by LLM (iteration 4): ensure coeff[0] == 1.0 after copying */
        coeff[0] := 1.0;
        
        /* code modified by LLM (iteration 4): update coefficients with proper bounds */
        i := val;
        while i > 0
            invariant 0 <= i <= val
            invariant coeff.Length == val + 1
            invariant coeff[0] == 1.0
            invariant val > 0
            invariant val - 1 < roots.Length
        {
            coeff[i] := coeff[i] - roots[val-1] * coeff[i-1];
            i := i - 1;
        }
    }
}