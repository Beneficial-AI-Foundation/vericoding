
//Problem01
//a)
// ATOM 

//b)
ghost function gcd'(x: int, y: int): int
    requires x > 0 && y > 0
{
    if x == y then x
    else if x > y then gcd'(x - y, y)
    else gcd(y, x)
}


// SPEC 

method gcdI(m: int, n: int) returns (d: int)
requires  m > 0 && n > 0 
ensures d == gcd(m, n);
{
}


//b)
// ATOM 

//b)
ghost function gcd'(x: int, y: int): int
    requires x > 0 && y > 0
{
    if x == y then x
    else if x > y then gcd'(x - y, y)
    else gcd(y, x)
}
'

 



 

