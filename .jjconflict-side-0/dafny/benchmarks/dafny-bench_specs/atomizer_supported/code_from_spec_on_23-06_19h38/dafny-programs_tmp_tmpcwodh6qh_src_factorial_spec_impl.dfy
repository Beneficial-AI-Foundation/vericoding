// ATOM 
function fact(n: nat): nat 
    ensures fact(n) >= 1
{
    if n == 0 then 1 else n * fact(n - 1)
}

//IMPL 
method factorial(n: nat) returns (res: nat)
    ensures res == fact(n)
{
    if n == 0 {
        res := 1;
    } else {
        var temp := factorial(n - 1);
        res := n * temp;
    }
}