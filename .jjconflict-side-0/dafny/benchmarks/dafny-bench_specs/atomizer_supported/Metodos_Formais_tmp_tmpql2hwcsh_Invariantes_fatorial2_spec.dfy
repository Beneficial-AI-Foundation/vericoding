// ATOM 
function Fat(n:nat):nat
{
    if n == 0 then 1 else n*Fat(n-1)
}


// SPEC 

method Fatorial(n:nat) returns (f:nat)
ensures f == Fat(n)
{
}


// i | n | variante
// 1 | 3 | 2
// 2 | 3 | 1
// 3 | 3 | 0
// 4 | 3 | -1
// variante = n - i
// então é usado o decreases n-1


// i | n | variante
// 1 | 3 | 2
// 2 | 3 | 1
// 3 | 3 | 0
// 4 | 3 | -1
// variante = n - i
// então é usado o decreases n-1
