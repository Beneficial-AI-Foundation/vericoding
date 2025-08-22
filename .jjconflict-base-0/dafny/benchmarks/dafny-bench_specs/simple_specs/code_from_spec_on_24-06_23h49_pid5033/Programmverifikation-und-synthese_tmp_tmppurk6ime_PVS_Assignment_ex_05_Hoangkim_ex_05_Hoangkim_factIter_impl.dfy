//ATOM
//# 2 pts

//Problem02
function fact(n:nat):nat
{if n==0 then 1 else n*fact(n-1)}


//IMPL 

method factIter(n:nat) returns (a:nat)
requires n >= 0
ensures a == fact(n)
{
    a := 1;
    var i := 0;
    
    while i < n
        invariant 0 <= i <= n
        invariant a == fact(i)
    {
        i := i + 1;
        a := a * i;
    }
}