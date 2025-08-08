//IMPL
method poly (roots: array<real>) returns (coeff: array<real>)
    requires roots.Length > 0; 
    ensures coeff.Length == roots.Length;
    ensures forall i :: 0 <= i < roots.Length ==> coeff[i] == poly_helper(roots, roots.Length - 1)[i];
{
    coeff := poly_helper(roots, roots.Length - 1);
}

//IMPL
method poly_helper (roots: array<real>, val: nat) returns (coeff: array<real>)
    requires roots.Length > 0; 
    requires val > 0 
    decreases val
    ensures coeff.Length == roots.Length;
    ensures coeff[0] == 1.0;
    ensures forall i :: 1 <= i < roots.Length - 1 ==> coeff[i] == poly_helper(roots, val+1)[i] + poly_helper(roots, val+1)[i-1]*roots[val];
    ensures if val == roots.Length - 1 then coeff[roots.Length - 1] == roots[roots.Length - 1] else coeff[roots.Length - 1] == poly_helper(roots, val+1)[i-1]*roots[val];
{
    coeff := new real[roots.Length];
    
    if val == 1 {
        // Base case: polynomial with one root
        coeff[0] := 1.0;
        if roots.Length > 1 {
            coeff[1] := -roots[0];
        }
        var i := 2;
        while i < roots.Length 
            invariant 2 <= i <= roots.Length
            invariant coeff[0] == 1.0
            invariant coeff[1] == -roots[0]
            invariant forall j :: 2 <= j < i ==> coeff[j] == 0.0
        {
            coeff[i] := 0.0;
            i := i + 1;
        }
    } else {
        // Recursive case
        var prev_coeff := poly_helper(roots, val - 1);
        
        // Initialize with previous coefficients
        coeff[0] := 1.0;
        var i := 1;
        while i < roots.Length
            invariant 1 <= i <= roots.Length
            invariant coeff[0] == 1.0
        {
            if i < prev_coeff.Length {
                coeff[i] := prev_coeff[i] - roots[val-1] * (if i > 0 then prev_coeff[i-1] else 0.0);
            } else {
                coeff[i] := 0.0;
            }
            i := i + 1;
        }
    }
}