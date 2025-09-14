// <vc-preamble>
predicate IsPrimePred(n: int)
{
    forall k :: 2 <= k < n ==> n % k != 0
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): added lemmas to prove postconditions and fixed function properties */
function IsPrime(n: int): bool
    requires n >= 1
{
    if n < 2 then false
    else forall k :: 2 <= k < n ==> n % k != 0
}

function FindLargestPrimeFactor(n: int, candidate: int): int
    requires 2 <= n
    requires 1 <= candidate <= n
    ensures 1 <= FindLargestPrimeFactor(n, candidate) <= n
    ensures FindLargestPrimeFactor(n, candidate) == 1 || (FindLargestPrimeFactor(n, candidate) > 1 && IsPrime(FindLargestPrimeFactor(n, candidate)))
    decreases candidate
{
    if candidate == 1 then 1
    else if n % candidate == 0 && IsPrime(candidate) then candidate
    else FindLargestPrimeFactor(n, candidate - 1)
}

lemma FindLargestPrimeFactorProperties(n: int, candidate: int)
    requires 2 <= n
    requires 1 <= candidate <= n
    ensures 1 <= FindLargestPrimeFactor(n, candidate) <= n
    ensures FindLargestPrimeFactor(n, candidate) == 1 || (FindLargestPrimeFactor(n, candidate) > 1 && IsPrimePred(FindLargestPrimeFactor(n, candidate)))
{
    var result := FindLargestPrimeFactor(n, candidate);
    if candidate == 1 {
        assert result == 1;
    } else if n % candidate == 0 && IsPrime(candidate) {
        assert result == candidate;
        assert IsPrime(candidate) == IsPrimePred(candidate);
    } else {
        FindLargestPrimeFactorProperties(n, candidate - 1);
    }
}
// </vc-helpers>

// <vc-spec>
method LargestPrimeFactor(n: int) returns (result: int)
    requires 2 <= n <= 2147483646
    ensures 1 <= result <= n
    ensures result == 1 || (result > 1 && IsPrimePred(result))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): added lemma call to prove postconditions */
    FindLargestPrimeFactorProperties(n, n);
    result := FindLargestPrimeFactor(n, n);
}
// </vc-code>
