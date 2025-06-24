//ATOM_PLACEHOLDER_add_by_inc

//IMPL Product
method Product(m: nat, n:nat) returns (res:nat)
ensures res == m*n;
{
    res := 0;
    var i := 0;
    
    while i < m
        invariant 0 <= i <= m
        invariant res == i * n
        decreases m - i
    {
        res := res + n;
        i := i + 1;
    }
}

//ATOM_PLACEHOLDER_gcdCalc

//ATOM_PLACEHOLDER_gcd

//ATOM_PLACEHOLDER_exp_by_sqr

//ATOM_PLACEHOLDER_exp