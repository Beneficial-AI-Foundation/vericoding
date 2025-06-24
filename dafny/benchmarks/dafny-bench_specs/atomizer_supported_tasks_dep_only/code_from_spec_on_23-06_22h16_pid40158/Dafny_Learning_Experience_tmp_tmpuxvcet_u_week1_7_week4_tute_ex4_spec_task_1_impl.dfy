// IMPL 
method LinearSearch<T>(a: array<T>, P: T -> bool) returns (n: int)
    ensures -1 <= n < a.Length
    ensures n == -1 || P(a[n])
    ensures n != -1 ==> forall i :: 0 <= i < n ==> ! P(a[i])
    ensures n == -1 ==> forall i :: 0 <= i < a.Length ==> ! P(a[i])
{
    /* code modified by LLM (iteration 1): Initialize n to 0 and add proper loop structure */
    n := 0;
    while n < a.Length
        invariant 0 <= n <= a.Length
        invariant forall i :: 0 <= i < n ==> !P(a[i])
    {
        if P(a[n]) {
            /* code modified by LLM (iteration 1): Return directly when element found, n already has correct value */
            return;
        }
        n := n + 1;
    }
    /* code modified by LLM (iteration 1): Set n to -1 when no element found, loop invariant ensures all elements checked */
    n := -1;
}