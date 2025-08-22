//ATOM_PLACEHOLDER_Max

//ATOM_PLACEHOLDER_Test

//ATOM_PLACEHOLDER_m1

// ATOM 

function fib (n: nat) : nat
{
    if n == 0 then 1 else
    if n == 1 then 1 else
    fib(n -1) + fib (n-2)
}

//IMPL Fib

method Fib (n: nat) returns (r:nat)
    ensures r == fib(n)
{
    if n == 0 {
        r := 1;
    } else if n == 1 {
        r := 1;
    } else {
        var prev := 1;
        var curr := 1;
        var i := 2;
        
        while i <= n
            invariant 2 <= i <= n + 1
            invariant prev == fib(i - 2)
            invariant curr == fib(i - 1)
        {
            var next := prev + curr;
            prev := curr;
            curr := next;
            i := i + 1;
        }
        
        r := curr;
    }
}

//ATOM_PLACEHOLDER_List//ATOM_PLACEHOLDER_add

//ATOM_PLACEHOLDER_addImp

//ATOM_PLACEHOLDER_MaxA