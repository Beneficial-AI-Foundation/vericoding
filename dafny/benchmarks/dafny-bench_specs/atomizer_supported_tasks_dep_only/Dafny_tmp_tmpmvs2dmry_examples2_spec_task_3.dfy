//ATOM_PLACEHOLDER_add_by_inc

//ATOM_PLACEHOLDER_Product

// SPEC 

method gcdCalc(m: nat, n: nat) returns (res: nat)
requires m>0 && n>0;
ensures res == gcd(m,n);
{
}


// ATOM 

function gcd(m: nat, n: nat) : nat
requires m>0 && n>0;
{
    if(m==n) then n 
    else if( m > n) then gcd(m-n,n)
    else gcd(m, n-m)
}


//ATOM_PLACEHOLDER_exp_by_sqr

//ATOM_PLACEHOLDER_exp

// method add_by_inc_vc(x: int, y:int) returns (z:int)
// {
//     assume x>=0 && y>=0;
//     z := x;
//     var i := 0;
//     assert 0 <= i <= y && z == x + i;
//     z,i = *,*;
//     assume 0 <= i <= y && z == x + i;
//     if (i < y) 
//     {
//         ghost var rank0 := y-i
//         z := z+1;
//         i := i+1; 
//         assert(y-i < rank0)
//         ghost var rank1 := y-i
//         assert(rank1 < rank0)
//         assert(rank1 >=0)
//         assert 0 <= i <= y && z == x + i;
//         assume(false);
//     }
//     assert (z == x+y);
//     assert (i == y);
//     return z;
// }




// method add_by_inc_vc(x: int, y:int) returns (z:int)
// {
//     assume x>=0 && y>=0;
//     z := x;
//     var i := 0;
//     assert 0 <= i <= y && z == x + i;
//     z,i = *,*;
//     assume 0 <= i <= y && z == x + i;
//     if (i < y) 
//     {
//         ghost var rank0 := y-i
//         z := z+1;
//         i := i+1; 
//         assert(y-i < rank0)
//         ghost var rank1 := y-i
//         assert(rank1 < rank0)
//         assert(rank1 >=0)
//         assert 0 <= i <= y && z == x + i;
//         assume(false);
//     }
//     assert (z == x+y);
//     assert (i == y);
//     return z;
// }


