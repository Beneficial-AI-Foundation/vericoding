//Problem01
// ATOM 

//Problem01
function fib(n: nat):nat
{
    if n < 2 then n else fib(n-2)+fib(n-1)
}

//IMPL fibIter
method fibIter(n:nat) returns (a:nat)
requires n > 0
ensures a == fib(n)
{
    if n == 1 {
        a := 1;
    } else {
        var i := 2;
        var prev := 0;
        var curr := 1;
        
        while i <= n
        invariant 2 <= i <= n + 1
        invariant prev == fib(i-2)
        invariant curr == fib(i-1)
        {
            var next := prev + curr;
            prev := curr;
            curr := next;
            i := i + 1;
        }
        
        a := curr;
    }
}

//# 2 pts

//Problem02
//ATOM_PLACEHOLDER_fact

//ATOM_PLACEHOLDER_factIter 
//# 3 pts
//Problem03
//ATOM_PLACEHOLDER_gcd

//ATOM_PLACEHOLDER_gcdI
//# 3 pts


// # sum: 9 pts















//# 3 pts


// # sum: 9 pts