// SPEC 
method add_by_inc(x: nat, y:nat) returns (z:nat)
ensures z == x+y;
{
}


// SPEC 

method Product(m: nat, n:nat) returns (res:nat)
ensures res == m*n;
{
}


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


// SPEC 

method exp_by_sqr(x0: real, n0: nat) returns (r:real)
requires x0 >= 0.0;
ensures r == exp(x0, n0);
{
}


// ATOM 

function exp(x: real, n: nat) :real
{
    if(n == 0) then 1.0
    else if (x==0.0) then 0.0
    else if (n  ==0 && x == 0.0) then 1.0
    else x*exp(x, n-1)
}


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


