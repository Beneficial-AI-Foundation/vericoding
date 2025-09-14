// <vc-preamble>
predicate IsDivisible(n: int, divisor: int)
    requires divisor != 0
{
    (n % divisor) == 0
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): Added comprehensive lemmas for prime existence proof */
lemma LemmaPrimeExists(n: int, k: int)
    requires n >= 2
    requires k >= 2
    requires k < n
    requires IsDivisible(n, k)
    ensures exists k' :: 2 <= k' < n && IsDivisible(n, k')
{
}

lemma LemmaPrimeNonexistent(n: int)
    requires n >= 2
    requires forall k :: 2 <= k < n ==> !IsDivisible(n, k)
    ensures !(exists k :: 2 <= k < n && IsDivisible(n, k))
{
}
// </vc-helpers>

// <vc-spec>
method IsNonPrime(n: int) returns (result: bool)
    requires n >= 2
    ensures result == (exists k :: 2 <= k < n && IsDivisible(n, k))
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): Fixed loop invariants and verification */
{
    var divisor := 2;
    result := false;
    
    while divisor < n
        invariant 2 <= divisor <= n
        invariant !result ==> (forall k :: 2 <= k < divisor ==> !IsDivisible(n, k))
        invariant result == (exists k :: 2 <= k < divisor && IsDivisible(n, k))
    {
        if IsDivisible(n, divisor) {
            result := true;
            LemmaPrimeExists(n, divisor);
            return;
        }
        divisor := divisor + 1;
    }
    
    if !result {
        LemmaPrimeNonexistent(n);
    }
}
// </vc-code>
