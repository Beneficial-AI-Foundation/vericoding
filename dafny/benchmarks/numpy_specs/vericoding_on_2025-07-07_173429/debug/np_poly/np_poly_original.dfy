//SPEC
method poly (roots: array<real>) returns (coeff: array<real>)
    requires roots.Length > 0; 
    ensures coeff.Length == roots.Length;
    ensures forall i :: 0 <= i < roots.Length ==> coeff[i] == poly_helper(roots, roots.Length - 1)[i]; //don't know how to fix
{} 

//SPEC
method poly_helper (roots: array<real>, val: nat) returns (coeff: array<real>)
    requires roots.Length > 0; 
    requires val > 0 
    decreases val
    ensures coeff.Length == roots.Length;
    ensures coeff[0] == 1.0;
    ensures forall i :: 1 <= i < roots.Length - 1 ==> coeff[i] == poly_helper(roots, val+1)[i] + poly_helper(roots, val+1)[i-1]*roots[val]; // fix this recursion bit
    ensures if val == roots.Length - 1 then coeff[roots.Length - 1] == roots[roots.Length - 1] else coeff[roots.Length - 1] == poly_helper(roots, val+1)[i-1]*roots[val];
{}