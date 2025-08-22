//ATOM_PLACEHOLDER_add_by_inc

//ATOM_PLACEHOLDER_Product

//IMPL gcdCalc
method gcdCalc(m: nat, n: nat) returns (res: nat)
requires m>0 && n>0;
ensures res == gcd(m,n);
{
    res := gcd(m, n);
}

//ATOM gcd
function gcd(m: nat, n: nat) : nat
requires m>0 && n>0;
{
    if(m==n) then n 
    else if( m > n) then gcd(m-n,n)
    else gcd(m, n-m)
}

//ATOM_PLACEHOLDER_exp_by_sqr

//ATOM_PLACEHOLDER_exp