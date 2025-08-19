//IMPL 

// n>=1 ==> 1 + 3 + 5 + ... + (2*n-1) = n*n

method Sqare(a:int) returns (x:int)
requires a>=1
ensures x == a*a
{
    x := a * a;
}