// ATOM 
function Fat(n:nat):nat
{
    if n == 0 then 1 else n*Fat(n-1)
}

// IMPL 
method Fatorial(n:nat) returns (f:nat)
ensures f == Fat(n)
{
    f := 1;
    var i := 1;
    
    while i <= n
        invariant 1 <= i <= n + 1
        invariant f == Fat(i - 1)
        decreases n - i
    {
        f := f * i;
        i := i + 1;
    }
}