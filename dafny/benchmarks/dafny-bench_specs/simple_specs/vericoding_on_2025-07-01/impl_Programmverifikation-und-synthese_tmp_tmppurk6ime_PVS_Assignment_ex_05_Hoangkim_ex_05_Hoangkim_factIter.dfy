//ATOM

//# 2 pts

//Problem02
function fact(n:nat):nat
{if n==0 then 1 else n*fact(n-1)}


// SPEC

method factIter(n:nat) returns (a:nat)
requires n >= 0
ensures a == fact(n)
{
}