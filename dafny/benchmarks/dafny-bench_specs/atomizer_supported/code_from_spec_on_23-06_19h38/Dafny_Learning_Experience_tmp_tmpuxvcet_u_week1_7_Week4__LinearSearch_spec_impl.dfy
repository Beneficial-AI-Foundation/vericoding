// IMPL 
method LinearSearch0<T>(a: array<T>, P: T -> bool) returns (n: int)
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

// IMPL 
method TestLinearSearch() {
    var a := new int[3];
    a[0] := 1;
    a[1] := 3;
    a[2] := 4;
    
    var result := LinearSearch0(a, P);
    /* code modified by LLM (iteration 1): Added assertions to help verification understand the properties */
    assert P(a[2]); // P(4) is true since 4 % 2 == 0
    assert !P(a[0]) && !P(a[1]); // P(1) and P(3) are false
    assert result == 2;
}

// IMPL 
method LinearSearch1<T>(a: array<T>, P: T -> bool) returns (n: int)
    ensures 0 <= n <= a.Length
    ensures n == a.Length || P(a[n])
    ensures n == a.Length ==> forall i :: 0 <= i < a.Length ==> !P(a[i])
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
    /* code modified by LLM (iteration 1): Added assertion to prove the third ensures clause when loop exits normally */
    assert n == a.Length;
    assert forall i :: 0 <= i < a.Length ==> !P(a[i]);
}