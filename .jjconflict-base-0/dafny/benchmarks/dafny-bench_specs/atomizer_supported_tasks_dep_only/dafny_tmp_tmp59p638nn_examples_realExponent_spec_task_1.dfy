
// ATOM 

ghost function power(n: real, alpha: real): real
    requires n > 0.0 && alpha > 0.0
    ensures power(n, alpha) > 0.0
//ATOM_PLACEHOLDER_log//ATOM_PLACEHOLDER_consistency//ATOM_PLACEHOLDER_logarithmSum// ATOM 

lemma powerLemma(n: real, alpha: real)
    requires n > 0.0 && alpha > 0.0
    ensures power(n, alpha) * alpha == power(n+1.0, alpha)
// ATOM 

lemma power1(alpha: real)
    requires alpha > 0.0
    ensures power(1.0, alpha) == alpha
//ATOM_PLACEHOLDER_test

//ATOM_PLACEHOLDER_test2

// SPEC 

method pow(n: nat, alpha: real) returns (product: real)
    requires n > 0
    requires alpha > 0.0
    ensures product == power(n as real, alpha)
{
}


