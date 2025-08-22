// ATOM 
predicate Par(n:int)
{
    n % 2 == 0
}


// SPEC 

method FazAlgo (a:int, b:int) returns (x:int, y:int)
requires a >= b && Par (a-b)
{
}


