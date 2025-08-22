// ATOM 
function Fib(n:nat):nat
{
    if n < 2
    then n
    else Fib(n-2) + Fib(n-1)
}

// IMPL ComputeFib
method ComputeFib(n:nat) returns (x:nat)
ensures x == Fib(n)
{
    if n < 2 {
        x := n;
    } else {
        var a := ComputeFib(n-2);
        var b := ComputeFib(n-1);
        x := a + b;
    }
}

//ATOM_PLACEHOLDER_Teste