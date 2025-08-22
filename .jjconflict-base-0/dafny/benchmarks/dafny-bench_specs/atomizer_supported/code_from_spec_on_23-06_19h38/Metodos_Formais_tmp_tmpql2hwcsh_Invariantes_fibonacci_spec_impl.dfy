// Provando fibonacci
//ATOM 
// Provando fibonacci
function Fib(n:nat):nat
{
    if n < 2
    then n
    else Fib(n-2) + Fib(n-1)
}

//IMPL 
method ComputeFib(n:nat) returns (x:nat)
ensures x == Fib(n)
{
    if n < 2 {
        x := n;
    } else {
        var i := 0;
        x := 0;
        var y := 1;
        
        while i < n
        invariant 0 <= i <= n
        invariant x == Fib(i)
        invariant y == Fib(i + 1)
        decreases n - i
        {
            var temp := x + y;
            x := y;
            y := temp;
            i := i + 1;
        }
    }
}