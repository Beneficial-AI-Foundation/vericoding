// ATOM 
 function Power(n:nat):nat 
{
    if n == 0 then 1 else 2 * Power(n-1)
}


// IMPL 

method CalcPower(n:nat) returns (p:nat)
    ensures p == 2*n;
{
    p := 2 * n;
}


// IMPL 

method ComputePower(n:nat) returns (p:nat)
    ensures p == Power(n)
{
    if n == 0 {
        p := 1;
    } else {
        var temp := ComputePower(n-1);
        p := 2 * temp;
    }
}