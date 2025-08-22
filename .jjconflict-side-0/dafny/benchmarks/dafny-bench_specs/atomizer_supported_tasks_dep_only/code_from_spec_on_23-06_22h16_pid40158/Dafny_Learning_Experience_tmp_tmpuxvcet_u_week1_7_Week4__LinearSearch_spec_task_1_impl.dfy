// IMPL 
method LinearSeach0<T>(a: array<T>, P: T -> bool) returns (n: int)
    ensures 0 <= n <= a.Length
    ensures n == a.Length || P(a[n])
{
    n := 0;
    while n < a.Length
        invariant 0 <= n <= a.Length
        invariant forall i :: 0 <= i < n ==> !P(a[i])
    {
        if P(a[n]) {
            return;
        }
        n := n + 1;
    }
}


// ATOM 

predicate P(n: int) {
    n % 2 == 0
}


//ATOM_PLACEHOLDER_TestLinearSearch

//ATOM_PLACEHOLDER_LinearSeach1